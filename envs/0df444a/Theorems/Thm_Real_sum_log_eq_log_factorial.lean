-- Prove2me | Theorems.Thm_Real_sum_log_eq_log_factorial
-- name    : Real.sum_log_eq_log_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:34.750817+00:00
-- url     : https://prove2.me/theorems/d9627a70-c107-4987-853e-81a27be9aaf0
-- title:
--   Real: sum log eq log factorial
-- statement:
--   The partial sum of the logarithm is equal to the log of the factorial.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L38-L40
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L38-L40

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

theorem Real.sum_log_eq_log_factorial : ∑ n ∈ Ioc 0 N, log n = log N.factorial := by sorry
