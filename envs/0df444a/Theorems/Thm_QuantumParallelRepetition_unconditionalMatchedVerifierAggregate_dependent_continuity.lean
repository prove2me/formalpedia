-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierAggregate_dependent_continuity
-- name    : QuantumParallelRepetition.unconditionalMatchedVerifierAggregate_dependent_continuity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/25bad353-8312-4062-9bc9-822309da2f80
-- title:
--   QuantumParallelRepetition.unconditionalMatchedVerifierAggregate_dependent_continuity
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

theorem QuantumParallelRepetition.unconditionalMatchedVerifierAggregate_dependent_continuity
    {J : Type*} [Fintype J]
    {H : J → Type*}
    [∀ j, NormedAddCommGroup (H j)]
    [∀ j, InnerProductSpace ℂ (H j)]
    (weight : J → ℝ)
    (nonnegative : ∀ j, 0 ≤ weight j)
    (effect : (j : J) → (H j →L[ℂ] H j))
    (contraction : ∀ j, ‖effect j‖ ≤ 1)
    (actual ideal : (j : J) → H j) :
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
      (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| ≤
      (Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) +
        Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2)) *
        Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) := by sorry
