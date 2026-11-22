-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_sqrt_margin_of_linear_budget
-- name    : PebblingLean.Hypercube.PaperParameters.stack_sqrt_margin_of_linear_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:00:08.908066+00:00
-- url     : https://prove2.me/theorems/ca3a2efb-590a-4602-b02d-7631cde9f4b6
-- title:
--   Paper Parameters: stack sqrt margin of linear budget
-- statement:
--   Once `K≥5A√3`, the stack sqrt coefficient is nonnegative, so the linear
--   margin alone can pay for the remaining logarithmic terms.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1327-L1348
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1327-L1348

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

theorem PebblingLean.Hypercube.PaperParameters.stack_sqrt_margin_of_linear_budget {A K : ℝ} {n : ℕ}
    (hKdom : 5 * A * Real.sqrt 3 ≤ K)
    (hbudget :
      2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
        ((3 : ℝ) * (n : ℝ) / 4) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
      ((K / 5 - A * Real.sqrt 3) * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) +
        ((3 : ℝ) * (n : ℝ) / 4) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by sorry
