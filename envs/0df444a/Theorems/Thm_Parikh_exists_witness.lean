-- Prove2me | Theorems.Thm_Parikh_exists_witness
-- name    : Parikh.exists_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:48.147698+00:00
-- url     : https://prove2.me/theorems/3d71bffe-d0ff-4fa4-9f15-9afa0821c691
-- title:
--   Parikh: exists witness
-- statement:
--   Mathlib's abstract semilinearity has an exact finite witness as well.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean#L111-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Counting.lean#L111-L135

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

theorem Parikh.exists_witness {T : Type*} (X : Set (Vector T)) (hX : IsSemilinearSet X) :
    ∃ W : Witness T, W.denotation = X := by sorry
