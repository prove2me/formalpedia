-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_div_five_real_lower_bound
-- name    : PebblingLean.Hypercube.PaperParameters.splitM_div_five_real_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:59.791148+00:00
-- url     : https://prove2.me/theorems/dfbfee31-1f2a-4a26-928f-c3fe47c23a84
-- title:
--   Paper Parameters: split M div five real lower bound
-- statement:
--   A floor-division lower bound for the recursive small dimension.  The
--   `-1` absorbs the integer division by five.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L435-L451
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L435-L451

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

theorem PebblingLean.Hypercube.PaperParameters.splitM_div_five_real_lower_bound {K : ℝ} {n : ℕ} :
    K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1 ≤
      ((splitM K n / 5 : ℕ) : ℝ) := by sorry
