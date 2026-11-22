-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_simple_budget_of_const_budget
-- name    : PebblingLean.Hypercube.PaperParameters.width_simple_budget_of_const_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:59:59.321683+00:00
-- url     : https://prove2.me/theorems/19418434-f748-4cd9-9ddb-513f188d0153
-- title:
--   Paper Parameters: width simple budget of const budget
-- statement:
--   A convenient way to pay the simplified width budget: use half of the
--   available `sqrt(n log n)` term for the constant and half for `5 log n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1529-L1559
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1529-L1559

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

theorem PebblingLean.Hypercube.PaperParameters.width_simple_budget_of_const_budget {K : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hconst :
      Real.log 128 + 4 * Real.log 2 ≤
        (K / 30 * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) :
    Real.log 128 + 4 * Real.log 2 + 5 * Real.log (n : ℝ) ≤
      (K / 15 * Real.log 2) *
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by sorry
