-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sqrt_three_n_log_eq
-- name    : PebblingLean.Hypercube.PaperParameters.sqrt_three_n_log_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:12.211724+00:00
-- url     : https://prove2.me/theorems/752285ce-ae2f-4338-bdb1-04e37f032e03
-- title:
--   Paper Parameters: sqrt three n log eq
-- statement:
--   The Paper Parameters construction uses the sqrt three n log eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1251-L1256
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1251-L1256

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

theorem PebblingLean.Hypercube.PaperParameters.sqrt_three_n_log_eq (n : ℕ) :
    Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) =
      Real.sqrt 3 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by sorry
