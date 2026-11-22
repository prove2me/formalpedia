-- Prove2me | Theorems.Thm_Real_le_sum_log
-- name    : Real.le_sum_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:16.614343+00:00
-- url     : https://prove2.me/theorems/9d173fae-6365-498c-96c3-ea901d025cdf
-- title:
--   Real: le sum log
-- statement:
--   A crude lower bound on the partial sum of the logarithm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L67-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L67-L85

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

theorem Real.le_sum_log (hx : 1 ≤ x) : x * log x - x - log x + 1 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by sorry
