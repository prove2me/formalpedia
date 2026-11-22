-- Prove2me | Theorems.Thm_Parikh_witness_isSemilinearSet
-- name    : Parikh.witness_isSemilinearSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:47.5181+00:00
-- url     : https://prove2.me/theorems/933698a2-f3df-4425-abab-3c250e615921
-- title:
--   Parikh: witness is Semilinear Set
-- statement:
--   Every explicit witness denotes a Mathlib semilinear set (`sec:statement`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean#L100-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean#L100-L108

module
public import Mathlib.Computability.Language
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Definitions.Def_LeanPool_Parikh_Counting
set_option autoImplicit true
@[expose] public section
public section
open scoped Pointwise
open Parikh

theorem Parikh.witness_isSemilinearSet {T : Type*} (W : Witness T) :
    IsSemilinearSet W.denotation := by sorry
