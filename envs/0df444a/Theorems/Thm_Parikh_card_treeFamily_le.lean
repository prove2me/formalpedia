-- Prove2me | Theorems.Thm_Parikh_card_treeFamily_le
-- name    : Parikh.card_treeFamily_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:37.297985+00:00
-- url     : https://prove2.me/theorems/a987d2db-a025-4982-b2a5-b9a384c59089
-- title:
--   Parikh: card tree Family le
-- statement:
--   Count each layer using finite union and function-space cardinalities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L139-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L139-L174

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

theorem Parikh.card_treeFamily_le (g : ContextFreeGrammar T) (b q : ℕ)
    (hq : 1 + Fintype.card T + (activeNonterminals g).card + g.rules.card ≤ q)
    (hb : ∀ r ∈ g.rules, r.output.length ≤ b) (H : ℕ) :
    (treeFamily g H).card ≤ q ^ heightPositions b H := by sorry
