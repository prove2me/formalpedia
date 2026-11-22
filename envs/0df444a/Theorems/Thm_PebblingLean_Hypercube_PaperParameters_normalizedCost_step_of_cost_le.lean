-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_normalizedCost_step_of_cost_le
-- name    : PebblingLean.Hypercube.PaperParameters.normalizedCost_step_of_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:15.815799+00:00
-- url     : https://prove2.me/theorems/b6f714ad-1537-474b-9efb-b4efd1f6b3d7
-- title:
--   Paper Parameters: normalized Cost step of cost le
-- statement:
--   Raw-cost form of the normalized recurrence step.  This is the algebraic
--   translation of
--   `|D_n| ≤ (1+n^{-2}) |D_m| (4/3)^a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2143-L2165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2143-L2165

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

theorem PebblingLean.Hypercube.PaperParameters.normalizedCost_step_of_cost_le {K : ℝ} {costBound : ℕ → ℕ} {n : ℕ}
    (hsplit : splitA K n + splitM K n = n)
    (hcostReal :
      (costBound n : ℝ) ≤
        (1 + loss n) * (((4 : ℝ) / 3) ^ splitA K n) *
          (costBound (splitM K n) : ℝ)) :
    normalizedCost costBound n ≤
      (1 + loss n) * normalizedCost costBound (splitM K n) := by sorry
