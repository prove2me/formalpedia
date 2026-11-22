-- Prove2me | Theorems.Thm_P2M_Real_le_sum_log__cffc06a55c87
-- name    : P2M_Real_le_sum_log__cffc06a55c87
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:46.718125+00:00
-- url     : https://prove2.me/theorems/8d9e175d-216c-4c39-a91c-a780c9b2f02d
-- title:
--   P2 M Real le sum log  cffc06a55c87: P2 M Real le sum log  cffc06a55c87
-- statement:
--   An even cruder lower bound on the partial sum of the logarithm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L88-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean#L88-L89

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

theorem P2M_Real_le_sum_log__cffc06a55c87 (hx : 1 ≤ x) : x * log x - 2 * x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by sorry

alias «Real».«le_sum_log'» := P2M_Real_le_sum_log__cffc06a55c87
