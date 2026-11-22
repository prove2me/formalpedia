-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_log_linear_budget_of_quadratic_threshold
-- name    : PebblingLean.Hypercube.PaperParameters.stack_log_linear_budget_of_quadratic_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:00:08.614797+00:00
-- url     : https://prove2.me/theorems/a12306c0-f710-4468-b406-7782fadec546
-- title:
--   Paper Parameters: stack log linear budget of quadratic threshold
-- statement:
--   Explicit threshold for the stack log-linear budget.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1486-L1525
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1486-L1525

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

theorem PebblingLean.Hypercube.PaperParameters.stack_log_linear_budget_of_quadratic_threshold {n : ℕ}
    (hthreshold : (32 / stackMargin ^ 2) ^ 2 ≤ (n : ℝ)) :
    16 * Real.log (n : ℝ) ≤
      (n : ℝ) *
        (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) ^ 2 := by sorry
