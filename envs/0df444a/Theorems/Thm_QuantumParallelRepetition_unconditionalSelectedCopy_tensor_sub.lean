-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopy_tensor_sub
-- name    : QuantumParallelRepetition.unconditionalSelectedCopy_tensor_sub
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/69fc44eb-8460-4b00-9899-147d17f583b0
-- title:
--   QuantumParallelRepetition.unconditionalSelectedCopy_tensor_sub
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.unconditionalSelectedCopy_tensor_sub
    {s τ : Type*} [Fintype s] [Fintype τ]
    (x y : EuclideanSpace ℂ s) (work : EuclideanSpace ℂ τ) :
    unconditionalMatchedVerifierTensor x work -
        unconditionalMatchedVerifierTensor y work =
      unconditionalMatchedVerifierTensor (x - y) work := by sorry
