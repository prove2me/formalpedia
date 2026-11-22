-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_condition_of_mean_upper
-- name    : PebblingLean.Hypercube.PaperParameters.log_condition_of_mean_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:30:50.434839+00:00
-- url     : https://prove2.me/theorems/2fc35455-b205-49a2-ae72-690f7489e8ff
-- title:
--   Paper Parameters: log condition of mean upper
-- statement:
--   Simplified Bernstein/union-bound logarithmic condition.  If the sampled
--   mean is at most `2t`, then the more legible lower bound
--   `delta^2 t/(128 B_0)` implies the logarithmic condition used by the
--   probabilistic-method finish.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1727-L1782
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1727-L1782

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

theorem PebblingLean.Hypercube.PaperParameters.log_condition_of_mean_upper {A K : ℝ} {n t : ℕ}
    (ht : 0 < t)
    (hmu_pos :
      0 < (sampleCountForDemand A K n t : ℝ) *
        (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hmu_upper :
      (sampleCountForDemand A K n t : ℝ) *
        (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) ≤
          2 * (t : ℝ))
    (hsimple :
      ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        (loss n) ^ 2 * (t : ℝ) /
          (128 * (2 ^ (rOut A K n - rIn A K n) : ℝ))) :
    ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
      (demandGapForDemand n t) ^ 2 /
        (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
          ((sampleCountForDemand A K n t : ℝ) *
            (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))) := by sorry
