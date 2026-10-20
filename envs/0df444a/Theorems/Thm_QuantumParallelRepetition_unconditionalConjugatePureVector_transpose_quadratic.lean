-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalConjugatePureVector_transpose_quadratic
-- name    : QuantumParallelRepetition.unconditionalConjugatePureVector_transpose_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/31730a1b-4ffb-4bf7-814d-22a2c82dd3ee
-- title:
--   QuantumParallelRepetition.unconditionalConjugatePureVector_transpose_quadratic
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

theorem QuantumParallelRepetition.unconditionalConjugatePureVector_transpose_quadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (z : EuclideanSpace ℂ ι) :
    quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M.transpose)
        (unconditionalConjugatePureVector z) =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M) z := by sorry
