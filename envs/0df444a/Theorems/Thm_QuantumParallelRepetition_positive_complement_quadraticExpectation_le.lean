-- Prove2me | Theorems.Thm_QuantumParallelRepetition_positive_complement_quadraticExpectation_le
-- name    : QuantumParallelRepetition.positive_complement_quadraticExpectation_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/a03ebe3b-719c-485a-b6cd-c320b9341a0f
-- title:
--   QuantumParallelRepetition.positive_complement_quadraticExpectation_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem QuantumParallelRepetition.positive_complement_quadraticExpectation_le
    (W : H →L[ℂ] H)
    (h_complement : (1 - W).IsPositive) (z : H) :
    quadraticExpectation W z ≤ ‖z‖ ^ 2 := by sorry
