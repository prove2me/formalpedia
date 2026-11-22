-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_const_budget_of_cutoff
-- name    : PebblingLean.Hypercube.PaperParameters.stack_const_budget_of_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:00:34.028855+00:00
-- url     : https://prove2.me/theorems/7c052034-6d02-4142-8561-14725a9f2daa
-- title:
--   Paper Parameters: stack const budget of cutoff
-- statement:
--   If the stack constant budget holds at the cutoff, then it holds for every
--   larger dimension because the linear margin is nonnegative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1661-L1678
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1661-L1678

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

theorem PebblingLean.Hypercube.PaperParameters.stack_const_budget_of_cutoff {n0 n : ℕ}
    (hn : n0 ≤ n)
    (hcutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    12 * Real.log 2 ≤
      (n : ℝ) *
        (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by sorry
