-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_log_budget_of_simplified_log_budget
-- name    : PebblingLean.Hypercube.PaperParameters.width_log_budget_of_simplified_log_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:53.693011+00:00
-- url     : https://prove2.me/theorems/6eac399b-1a85-4665-adaf-40f3371dbc44
-- title:
--   Paper Parameters: width log budget of simplified log budget
-- statement:
--   A cleaner sufficient form of the residual width budget.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1392-L1414
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1392-L1414

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

theorem PebblingLean.Hypercube.PaperParameters.width_log_budget_of_simplified_log_budget {K : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hbudget :
      Real.log 128 + 4 * Real.log 2 + 5 * Real.log (n : ℝ) ≤
        (K / 15 * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) :
    Real.log 128 + 3 * Real.log 2 +
        Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
        4 * Real.log (n : ℝ) ≤
      (K / 15 * Real.log 2) *
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by sorry
