-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_logSimple_for_all_demands_of_minPile
-- name    : PebblingLean.Hypercube.PaperParameters.logSimple_for_all_demands_of_minPile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:00.975806+00:00
-- url     : https://prove2.me/theorems/394edde7-4eaf-4ded-8cc6-7edbc6c36fc8
-- title:
--   Paper Parameters: log Simple for all demands of min Pile
-- statement:
--   Since the simplified Bernstein exponent is linear in the demand `t`, it
--   is enough to check it at the smallest allowed demand.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1871-L1905
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1871-L1905

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

theorem PebblingLean.Hypercube.PaperParameters.logSimple_for_all_demands_of_minPile {A K : ℝ} {n : ℕ}
    (hmin :
      ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
          (128 * (2 ^ (rOut A K n - rIn A K n) : ℝ))) :
    ∀ t : ℕ, minPile (splitM K n) ≤ t →
      ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        (loss n) ^ 2 * (t : ℝ) /
          (128 * (2 ^ (rOut A K n - rIn A K n) : ℝ)) := by sorry
