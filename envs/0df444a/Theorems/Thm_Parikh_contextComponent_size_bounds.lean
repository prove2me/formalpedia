-- Prove2me | Theorems.Thm_Parikh_contextComponent_size_bounds
-- name    : Parikh.contextComponent_size_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:38.65696+00:00
-- url     : https://prove2.me/theorems/fc0fa63e-1101-44b7-813b-062ed10205c2
-- title:
--   Parikh: context Component size bounds
-- statement:
--   A component has one period per context and pays all first copies in its base.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean#L148-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean#L148-L168

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Data.Nat.Log
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Parikh_Construction
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.contextComponent_size_bounds {T N : Type*} [Fintype T] [DecidableEq T]
    (B : ParseTree T N) (D : Finset (ParseTree T N)) (M : ℕ)
    (hB : norm B.weight ≤ M) (hD : ∀ C ∈ D, norm C.weight ≤ M) :
    (contextComponent B D).periods.length = D.card ∧
      norm (contextComponent B D).base ≤ (D.card + 1) * M ∧
      ∀ p ∈ (contextComponent B D).periods, norm p ≤ M := by sorry
