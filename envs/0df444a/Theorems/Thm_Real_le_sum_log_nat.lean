-- Prove2me | Theorems.Thm_Real_le_sum_log_nat
-- name    : Real.le_sum_log_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:22.978186+00:00
-- url     : https://prove2.me/theorems/aa826497-c03e-406f-8ae4-9374b5b80816
-- title:
--   Real: le sum log nat
-- statement:
--   A sharper bound on the partial sum of the logarithm in the natural number case.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L92-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L92-L98

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

theorem Real.le_sum_log_nat : N * log N - N ≤ ∑ n ∈ Ioc 0 N, log n := by sorry
