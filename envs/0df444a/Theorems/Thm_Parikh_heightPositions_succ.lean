-- Prove2me | Theorems.Thm_Parikh_heightPositions_succ
-- name    : Parikh.heightPositions_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:33.614798+00:00
-- url     : https://prove2.me/theorems/cab022cd-8b5b-42d4-bd24-4584e998c939
-- title:
--   Parikh: height Positions succ
-- statement:
--   The Parikh construction uses the height Positions succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L38-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L38-L44

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.heightPositions_succ (b H : ℕ) :
    heightPositions b (H + 1) = 1 + b * heightPositions b H := by sorry
