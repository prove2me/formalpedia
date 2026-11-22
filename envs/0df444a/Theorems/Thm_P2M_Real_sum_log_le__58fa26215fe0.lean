-- Prove2me | Theorems.Thm_P2M_Real_sum_log_le__58fa26215fe0
-- name    : P2M_Real_sum_log_le__58fa26215fe0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:43.169448+00:00
-- url     : https://prove2.me/theorems/393c0d2c-d8f6-4faf-8d11-55409d3b0a89
-- title:
--   P2 M Real sum log le  58fa26215fe0: P2 M Real sum log le  58fa26215fe0
-- statement:
--   An even cruder upper bound on the partial sum of the logarithm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L63-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L63-L64

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

theorem P2M_Real_sum_log_le__58fa26215fe0 (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x := by sorry

alias «Real».«sum_log_le'» := P2M_Real_sum_log_le__58fa26215fe0
