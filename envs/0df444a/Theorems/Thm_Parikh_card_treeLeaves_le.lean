-- Prove2me | Theorems.Thm_Parikh_card_treeLeaves_le
-- name    : Parikh.card_treeLeaves_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:23.292174+00:00
-- url     : https://prove2.me/theorems/222b0215-37df-4f5b-acc4-10af50951596
-- title:
--   Parikh: card tree Leaves le
-- statement:
--   The Parikh construction uses the card tree Leaves le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L100-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L100-L105

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

theorem Parikh.card_treeLeaves_le (g : ContextFreeGrammar T) :
    (treeLeaves g).card ≤ Fintype.card T + (activeNonterminals g).card := by sorry
