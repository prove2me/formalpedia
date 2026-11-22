-- Prove2me | Theorems.Thm_Parikh_ContextsActivatable_realize
-- name    : Parikh.ContextsActivatable.realize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:15.467554+00:00
-- url     : https://prove2.me/theorems/f2ff306f-f932-4447-9b5f-6a81901025a4
-- title:
--   Contexts Activatable: realize
-- statement:
--   Introduce each selected context once, with exact accounting and every
--   selected context enabled afterwards (`lem:activation-realize`, `eq:activated-wt/supp`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L231-L259
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L231-L259

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

theorem Parikh.ContextsActivatable.realize {T : Type*} [DecidableEq T]
    {g : ContextFreeGrammar T} {B : ParseTree T g.NT} {D : Finset (ParseTree T g.NT)}
    (hD : ContextsActivatable g B D) (hB : Complete g B) :
    ∃ order t, order.Nodup ∧ (∀ C, C ∈ order ↔ C ∈ D) ∧
      InsertionSequence g B order t ∧ Complete g t ∧ t.root = B.root ∧
      t.weight = B.weight + ∑ C ∈ D, C.weight ∧
      t.support = B.support ∪ ⋃ C ∈ D, C.support ∧
      ∀ C ∈ D, ∃ t', Inserts g t C t' := by sorry
