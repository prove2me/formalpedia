-- Prove2me | Theorems.Thm_Real_sum_log_le
-- name    : Real.sum_log_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:38.379887+00:00
-- url     : https://prove2.me/theorems/2afc6fdd-c4b9-4c75-aa72-dcb50baa62b0
-- title:
--   Real: sum log le
-- statement:
--   A crude upper bound on the partial sum of the logarithm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L49-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L49-L60

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

theorem Real.sum_log_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1 := by sorry
