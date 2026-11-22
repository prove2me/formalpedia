-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_ceilingSq_of_pow_half
-- name    : PebblingLean.Hypercube.PaperParameters.ceilingSq_of_pow_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:14.972549+00:00
-- url     : https://prove2.me/theorems/7c1ce7e5-a0ea-4c42-b7ed-743b1e28777d
-- title:
--   Paper Parameters: ceiling Sq of pow half
-- statement:
--   It is enough for ceiling slack to prove the still coarser growth estimate
--   `n^2 ≤ (4/3)^(n/2)`, because the split condition gives `n/2 ≤ a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2013-L2018
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2013-L2018

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

theorem PebblingLean.Hypercube.PaperParameters.ceilingSq_of_pow_half {K : ℝ} {n : ℕ}
    (hhalf : n / 2 ≤ splitA K n)
    (hpow : (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ (n / 2))) :
    (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ splitA K n) := by sorry
