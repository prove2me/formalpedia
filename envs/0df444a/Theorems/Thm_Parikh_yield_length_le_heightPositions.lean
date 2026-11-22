-- Prove2me | Theorems.Thm_Parikh_yield_length_le_heightPositions
-- name    : Parikh.yield_length_le_heightPositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:39.588029+00:00
-- url     : https://prove2.me/theorems/a365cd4f-eaa3-446d-8d52-105505d2cde2
-- title:
--   Parikh: yield length le height Positions
-- statement:
--   Valid trees have at most the full branching-tree budget of terminal leaves.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L178-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L178-L219

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [Fintype T]
omit [Fintype T]

theorem Parikh.yield_length_le_heightPositions (g : ContextFreeGrammar T) (b : ℕ)
    (hb : ∀ r ∈ g.rules, r.output.length ≤ b) (H : ℕ) (t : ParseTree T g.NT)
    (hv : Valid g t) (hh : t.height ≤ H) : t.yield.length ≤ heightPositions b H := by sorry
