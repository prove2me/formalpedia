-- Prove2me | Theorems.Thm_Parikh_heightPositions_pos
-- name    : Parikh.heightPositions_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:13.980455+00:00
-- url     : https://prove2.me/theorems/440e20fe-7c38-418d-9fe4-400f244cdfb9
-- title:
--   Parikh: height Positions pos
-- statement:
--   The Parikh construction uses the height Positions pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L46-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L46-L49

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.heightPositions_pos (b H : ℕ) : 1 ≤ heightPositions b H := by sorry
