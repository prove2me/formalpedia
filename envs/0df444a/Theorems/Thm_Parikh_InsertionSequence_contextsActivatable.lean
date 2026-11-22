-- Prove2me | Theorems.Thm_Parikh_InsertionSequence_contextsActivatable
-- name    : Parikh.InsertionSequence.contextsActivatable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:28.901875+00:00
-- url     : https://prove2.me/theorems/1540cd01-4c44-491b-977f-6b6472736c63
-- title:
--   Insertion Sequence: contexts Activatable
-- statement:
--   The distinct contexts used by an insertion sequence are activatable from
--   its complete base (`lem:first-occurrence`, `thm:main`). Context identities are retained.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L360-L385
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L360-L385

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.InsertionSequence.contextsActivatable {T : Type*} {g : ContextFreeGrammar T}
    {B t : ParseTree T g.NT} {Cs : List (ParseTree T g.NT)}
    [DecidableEq (ParseTree T g.NT)]
    (h : InsertionSequence g B Cs t) (hB : Complete g B) :
    ContextsActivatable g B Cs.toFinset := by sorry
