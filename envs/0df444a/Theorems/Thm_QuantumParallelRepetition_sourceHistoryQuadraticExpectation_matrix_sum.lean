-- Prove2me | Theorems.Thm_QuantumParallelRepetition_sourceHistoryQuadraticExpectation_matrix_sum
-- name    : QuantumParallelRepetition.sourceHistoryQuadraticExpectation_matrix_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/c5b96c73-7156-4745-8af7-0bcf1aca700f
-- title:
--   QuantumParallelRepetition.sourceHistoryQuadraticExpectation_matrix_sum
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
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.sourceHistoryQuadraticExpectation_matrix_sum
    {I d : Type*} [Fintype I] [Fintype d] [DecidableEq d]
    (M : I → Matrix d d ℂ) (z : EuclideanSpace ℂ d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (∑ i : I, M i)) z =
      ∑ i : I,
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (M i)) z := by sorry
