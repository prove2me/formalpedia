-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_explicitConstants_cutoff_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_explicitConstants_cutoff_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:18.493899+00:00
-- url     : https://prove2.me/theorems/b8504294-910d-4b0d-b4ef-872dd7a12143
-- title:
--   Paper Parameters: has Real Upper Bound of explicit Constants cutoff finite Base
-- statement:
--   Explicit-constant version with `A=4` and `K=217`.  All structural
--   constant inequalities are discharged; what remains is a finite list of cutoff
--   checks at `n0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5508-L5556
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5508-L5556

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_explicitConstants_cutoff_finiteBase
    {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hwidthFitThreshold :
      (128 * ((4 : ℝ) * Real.sqrt 3) ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hcoreNineCutoff :
      81 ≤ (4 : ℝ) ^ 2 * (((3 : ℝ) * (n0 : ℝ) / 4) *
        Real.log (n0 : ℝ)))
    (hwidthConstCutoff :
      Real.log 128 + 4 * Real.log 2 ≤
        ((217 : ℝ) / 30 * Real.log 2) *
          Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)))
    (hstackLogThreshold :
      (32 / stackMargin ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hstackConstCutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound 217 n0) n0) := by sorry
