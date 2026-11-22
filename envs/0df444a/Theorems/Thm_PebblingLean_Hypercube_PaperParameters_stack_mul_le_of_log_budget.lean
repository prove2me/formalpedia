-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_mul_le_of_log_budget
-- name    : PebblingLean.Hypercube.PaperParameters.stack_mul_le_of_log_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:59:15.529795+00:00
-- url     : https://prove2.me/theorems/c3c77318-8369-406b-907d-3c7c503a2d11
-- title:
--   Paper Parameters: stack mul le of log budget
-- statement:
--   Logarithmic sufficient condition for the multiplication-form stack
--   threshold.  This rewrites
--   `2 n^2 2^rOut ≤ 2^(m/5) (4/3)^a` as a comparison of logarithms.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L900-L943
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L900-L943

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

theorem PebblingLean.Hypercube.PaperParameters.stack_mul_le_of_log_budget {A K : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hlog :
      Real.log 2 + 2 * Real.log (n : ℝ) +
          (rOut A K n : ℝ) * Real.log 2 ≤
        ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
          (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3)) :
    2 * ((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ) ≤
      (minPile (splitM K n) : ℝ) *
        (((4 : ℝ) / 3) ^ splitA K n) := by sorry
