-- Prove2me | Theorems.Thm_QuantumParallelRepetition_mixtureBlockMatrix_trace_mul
-- name    : QuantumParallelRepetition.mixtureBlockMatrix_trace_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/b935d1e5-ef5b-4036-a70b-7be0631a7edf
-- title:
--   QuantumParallelRepetition.mixtureBlockMatrix_trace_mul
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
variable {X Y A B : Type*} {J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype J] [DecidableEq J]
variable {G : Game X Y A B}

theorem QuantumParallelRepetition.mixtureBlockMatrix_trace_mul
    (p : J → ℝ) (S : J → Strategy G)
    (E : ∀ j : J,
      Matrix ((S j).Alice × (S j).Bob)
        ((S j).Alice × (S j).Bob) ℂ) :
    Matrix.trace (mixtureBlockMatrix p S * Matrix.blockDiagonal' E) =
      ∑ j : J, p j • Matrix.trace ((S j).state.matrix * E j) := by sorry
