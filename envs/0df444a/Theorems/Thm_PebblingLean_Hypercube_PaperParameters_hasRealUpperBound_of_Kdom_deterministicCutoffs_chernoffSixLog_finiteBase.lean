-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffSixLog_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffSixLog_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:08.261952+00:00
-- url     : https://prove2.me/theorems/a571256e-1059-4738-b60b-5ceb7e0e7c79
-- title:
--   Paper Parameters: has Real Upper Bound of Kdom deterministic Cutoffs chernoff Six Log finite Base
-- statement:
--   Chernoff wrapper with the natural choice `E_n = 6 log n`.  The two
--   structural Chernoff side conditions `rIn≤a/3-w` and `λ≤1` are both discharged
--   from the single annulus condition `3w≤a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5121-L5177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5121-L5177

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffSixLog_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hsplitThreshold : (128 * K ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hthreeWidth :
      ∀ n : ℕ, n0 ≤ n →
        3 * annulusWidth A K n ≤ splitA K n)
    (hwidthNine :
      ∀ n : ℕ, n0 ≤ n →
        9 ≤ (annulusWidth A K n : ℝ))
    (hchernoffSix :
      ∀ n : ℕ, n0 ≤ n →
        6 * Real.log (n : ℝ) ≤
          (1 / 2) *
            ((annulusWidth A K n : ℝ) ^ 2 /
              ((splitA K n : ℝ) + 1)))
    (hwidthConstCutoff :
      Real.log 128 + 4 * Real.log 2 ≤
        (K / 30 * Real.log 2) *
          Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)))
    (hstackLogThreshold :
      (32 / stackMargin ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hstackConstCutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
