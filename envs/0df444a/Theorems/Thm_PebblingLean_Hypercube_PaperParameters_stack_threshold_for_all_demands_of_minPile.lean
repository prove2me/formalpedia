-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_threshold_for_all_demands_of_minPile
-- name    : PebblingLean.Hypercube.PaperParameters.stack_threshold_for_all_demands_of_minPile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:45.095769+00:00
-- url     : https://prove2.me/theorems/b9a61f6d-996b-422f-b98c-64a3b8af3506
-- title:
--   Paper Parameters: stack threshold for all demands of min Pile
-- statement:
--   To verify the stack-size threshold for all allowed demands, it is enough
--   to verify it at the smallest allowed demand `minPile(splitM n)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L838-L868
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L838-L868

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

theorem PebblingLean.Hypercube.PaperParameters.stack_threshold_for_all_demands_of_minPile {A K : ℝ} {n : ℕ}
    (hmin :
      (2 ^ rOut A K n : ℝ) ≤
        (loss n / 2) * (minPile (splitM K n) : ℝ) *
          (((4 : ℝ) / 3) ^ splitA K n)) :
    ∀ t : ℕ, minPile (splitM K n) ≤ t →
      (2 ^ rOut A K n : ℝ) ≤
        (loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n) := by sorry
