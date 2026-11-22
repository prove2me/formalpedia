-- Prove2me | Theorems.Thm_Real_sum_log_add_one_eq_log_factorial
-- name    : Real.sum_log_add_one_eq_log_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:39.871793+00:00
-- url     : https://prove2.me/theorems/34d12ba4-59b3-42a0-b4df-08e570a9e61e
-- title:
--   Real: sum log add one eq log factorial
-- statement:
--   The partial sum of the logarithm, in `Finset.range` form: `∑ n ∈ range N, log (n + 1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L43-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L43-L46

module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SumIntegralComparisons
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
set_option autoImplicit true
@[expose] public section
public section
open Nat hiding log log_pos
open Finset intervalIntegral MeasureTheory
open Real
variable {x : ℝ} (N : ℕ)

theorem Real.sum_log_add_one_eq_log_factorial : ∑ n ∈ range N, log (n + 1) = log N.factorial := by sorry
