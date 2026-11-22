-- Prove2me | Theorems.Thm_Parikh_ParseTree_card_nodeFamily_le
-- name    : Parikh.ParseTree.card_nodeFamily_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:21.103752+00:00
-- url     : https://prove2.me/theorems/e48aa9b5-c6b5-4fe6-8084-ee447a3dcfe1
-- title:
--   Parse Tree: card node Family le
-- statement:
--   The Parse Tree construction uses the card node Family le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L80-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L80-L83

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.ParseTree
variable {T N : Type*}

theorem Parikh.ParseTree.card_nodeFamily_le (r : ContextFreeRule T N) (family : Finset (ParseTree T N)) :
    (nodeFamily r family).card ≤ family.card ^ r.output.length := by sorry
