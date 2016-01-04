#!/usr/bin/env swift
//: Playground - noun: a place where people can play

//: LC : Implemements a minimal simply-typed lambda calculus with unit, ints and addition.
//: In this version, we use nil instead of exceptions to avoid polluting the type signatures.

var Binops = [
    "+": {(a: Int,b: Int) -> Int in
        return a + b} , //Lambda syntax in swift: lambda x : T1 . e : T1 -> T2 is {(x: T1) -> T2 in return e}
]

typealias Id = String

indirect enum Type{
    case Unit
    case Int
    case Fun([Type], Type)// [Type] = listof Type
}

// Equality of Types.
extension Type: Equatable { }
func ==(a:Type, b:Type) -> Bool {
        switch a {
        case Type.Unit:
                switch b{
                case Type.Unit:
                    return true
                default:
                    return false
                }
        case Type.Int:
                switch b{
                case Type.Int:
                    return true
                default:
                    return false
                }
        case let Type.Fun(adom,arng):
                switch b{
                case let Type.Fun(bdom, brng):
                    return zip(adom,bdom).reduce(true, combine: {(acc:Bool,dom:(a:Type,b:Type)) -> Bool in acc && dom.a == dom.b}) && arng == brng
                default:
                    return false 
                }
        }
}


//equivalent to #lang plai's define-type.
indirect enum Expr{ //indirect keyword is required for the recursion.
    case Unit
    case Lambda([(Id, Type)], Expr) //Multiargument lambda.
    case App(Expr, [Expr])
    case Int(Swift.Int) //Name collision: disambiguate by using Library name :)
    case Binop(Id, Expr, Expr)
    case Ident(Id)
}

//definition of substitution function.
func subst(e:Expr, x:Id, v:Expr) -> Expr{
    switch e{
    case .Unit:
        return e
    case .Int(_):
        return e
    case let .Binop(f, op1, op2):
        return Expr.Binop(f, subst(op1, x: x, v: v), subst(op2, x: x, v: v))
    case let .App(f, args):
        return Expr.App(subst(f,x: x,v: v), args.map({(arg: Expr) -> Expr in subst(arg,x: x, v: v)}))
    case let .Lambda(ids, body):
        if ids.map({(p:(x:Id, T: Type)) -> Id in x}).contains(x) {
            return e
        } else { 
            return Expr.Lambda(ids, subst(body,x: x, v: v))
        }
    case let .Ident(y):
        if (x == y) {
            return v
        } else {
            return e
        }
    }
}

//Helper function, mimics scheme's andmap.
func andmap<T>(list: [T], check:(T) -> Bool) -> Bool{
    return list.reduce(true, combine: {(acc: Bool, element:T) -> Bool in acc && check(element)})
}

//helper function to create a lambda wrapper for the combine function that also accepts nil for arguments.
//useful for fold (in swift terms, reduce, which requires a "combine" lambda)
func combine_opt<T,U>(combine: (T, U) -> T?) -> ((T?, U?) -> T?){
    return {(acc: T?, v: U?) -> T? in
        if let accv = acc {
            if let vv = v {
                return combine(accv,vv)
            }
        }
        return nil
    }
}

//Evaluator. Mimics a big-step semantics.
func eval(e: Expr) -> Expr?{
    switch e{
    case .Unit:
        return e
    case .Int(_):
        return e
    case .Lambda(_, _ ):
        return e
    case .Ident(_):
        return nil 
    case let .Binop(f, op1, op2):
        if (Binops[f] != nil) {
            if let v1 = eval(op1) {
                switch v1{
                case let .Int(x):
                    if let v2 = eval(op2) {
                        switch v2{
                        case let Expr.Int(y):
                            return Expr.Int(Binops[f]!(x,y))
                        default:
                            return nil
                        }
                    }
                default:
                    return nil
                }
            }
        }
    case let .App(f, args):
        if let fv = eval(f) {
            switch fv{
            case let .Lambda(ids, body):
                return zip(ids,args).reduce(body, combine: combine_opt({(acc: Expr, pair: (y: (id:Id, T:Type), ey:Expr)) -> Expr? in
                    if let vy=eval(pair.ey) {
                            return subst(acc, x:pair.y.id, v: vy)
                        } else {
                            return nil
                    }}))
            default:
                return nil
            }
        }
    }
    return nil 
}

//an environment is a dictionary from identifiers to types.
typealias Env = [Id:Type]

let emptyEnv: Env = [Id:Type]()

func extend_env(e:Env, with:[(Id, Type)]) -> Env{
    var new_env = e
    for (x,T) in with{
        new_env[x]=T
    }
    return new_env
}

func typecheck(e: Expr, env: Env) -> Type? {
    switch e {
    case Expr.Unit:
        return Type.Unit
    case Expr.Int(_):
        return Type.Int
    case let Expr.Ident(x):
        return env[x]
    case let Expr.Binop(id,op1,op2):
        //for now, this case is assuming that all binops are Int x Int -> Int
        if (typecheck(op1,env: env) == Type.Int) && (typecheck(op2, env: env) == Type.Int){
                        if (Binops[id] != nil){
                            return Type.Int
                        }
        }
        return nil
    case let Expr.Lambda(args, body):
        return Type.Fun(args.map({(arg:(x: Id, T: Type)) -> Type in arg.T}),
                        typecheck(body, env: extend_env(env,with:args))!)
    case let Expr.App(f, args):
        if let tf = typecheck(f, env: env) {
            switch tf{
            case let Type.Fun(dom, rng):
                if dom.count == args.count {
                    if andmap(Array(zip(args,dom)), check:{(arg:(e:Expr, T:Type)) -> Bool in
                        return arg.T == typecheck(arg.e,env: env)}){
                            return rng
                    } else {
                        return nil
                    }
                } else {
                    return nil
                }
            default:
                return nil
            }
        }
    }
    return nil 
}

func test<T: Equatable>(value:T?,expect:T?){
    if let v=value{
        if let x=expect{
            if x==v{
                print("Test passed for \(value)")
            } else {
                print("ERROR: Expected \(x), Got \(v)")
            }
        } else {
            print("ERROR: Expected nil, Got \(v)")
        }
    } else {
        if let x=expect{
            print("ERROR: Expected \(x), got nil")
        } else {
            print("Test passed for nil")
        }
    }
}

print(typecheck(Expr.Lambda([("x", Type.Unit)], Expr.Ident("x") ), env: emptyEnv))
print(Type.Fun([Type.Unit], Type.Unit))
print(Type.Unit == Type.Unit)
test(
    typecheck(Expr.Lambda([("x", Type.Unit)], Expr.Ident("x") ), env: emptyEnv),
    expect: Type.Fun([Type.Unit],Type.Unit)
    )
