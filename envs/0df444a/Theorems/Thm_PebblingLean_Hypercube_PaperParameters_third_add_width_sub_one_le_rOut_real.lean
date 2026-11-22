-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_third_add_width_sub_one_le_rOut_real
-- name    : PebblingLean.Hypercube.PaperParameters.third_add_width_sub_one_le_rOut_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:58:31.074089+00:00
-- url     : https://prove2.me/theorems/7ae8c8ae-7546-4928-86e3-733963bec9c6
-- title:
--   Paper Parameters: third add width sub one le r Out real
-- statement:
--   The outer radius is at least `a/3+w-1`; the `1` is the floor slack from
--   integer division by `3`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L497-L504
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L497-L504

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters

theorem PebblingLean.Hypercube.PaperParameters.third_add_width_sub_one_le_rOut_real {A K : ℝ} {n : ℕ} :
    (splitA K n : ℝ) / 3 + (annulusWidth A K n : ℝ) - 1 ≤
      (rOut A K n : ℝ) := by sorry
