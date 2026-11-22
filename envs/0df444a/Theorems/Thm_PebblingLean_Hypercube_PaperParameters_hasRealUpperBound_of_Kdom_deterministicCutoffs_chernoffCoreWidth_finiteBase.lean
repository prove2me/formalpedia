-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffCoreWidth_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffCoreWidth_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:10.256162+00:00
-- url     : https://prove2.me/theorems/a22a412b-2356-4779-8738-c42e92b44dad
-- title:
--   Paper Parameters: has Real Upper Bound of Kdom deterministic Cutoffs chernoff Core Width finite Base
-- statement:
--   Core-width version of the final Chernoff wrapper.  The remaining Chernoff
--   side conditions are now stated using the real expression
--   `A sqrt(a log(2n^2))` inside the width ceiling:
--
--   * `3(core+1)≤a` makes the actual integer width satisfy `3w≤a`;
--   * `core≥9` gives the right-tail floor-slack condition;
--   * `12(a+1)log n≤core^2` gives the six-log Chernoff exponent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5237-L5294
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5237-L5294

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffCoreWidth_finiteBase
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hsplitThreshold : (128 * K ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hthreeWidthCore :
      ∀ n : ℕ, n0 ≤ n →
        3 * (annulusWidthCore A K n + 1) ≤ (splitA K n : ℝ))
    (hwidthCoreNine :
      ∀ n : ℕ, n0 ≤ n →
        9 ≤ annulusWidthCore A K n)
    (hchernoffCoreSq :
      ∀ n : ℕ, n0 ≤ n →
        12 * ((splitA K n : ℝ) + 1) * Real.log (n : ℝ) ≤
          (annulusWidthCore A K n) ^ 2)
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
