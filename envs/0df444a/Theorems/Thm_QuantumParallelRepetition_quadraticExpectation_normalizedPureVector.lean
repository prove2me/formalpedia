-- Prove2me | Theorems.Thm_QuantumParallelRepetition_quadraticExpectation_normalizedPureVector
-- name    : QuantumParallelRepetition.quadraticExpectation_normalizedPureVector
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/98c04d4e-530e-498c-9a9c-c10cc32ef324
-- title:
--   QuantumParallelRepetition.quadraticExpectation_normalizedPureVector
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
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.quadraticExpectation_normalizedPureVector
    {d : Type*} [Fintype d]
    (W : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)
    (z : EuclideanSpace ℂ d) :
    quadraticExpectation W (normalizedPureVector z) =
      quadraticExpectation W z / ‖z‖ ^ 2 := by sorry
