-- Prove2me | Theorems.Thm_QuantumParallelRepetition_mixtureEmbedding_compress
-- name    : QuantumParallelRepetition.mixtureEmbedding_compress
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/eda8500d-249f-44c8-85c0-f6861959eaff
-- title:
--   QuantumParallelRepetition.mixtureEmbedding_compress
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

theorem QuantumParallelRepetition.mixtureEmbedding_compress (S : J → Strategy G)
    (E : Matrix (mixtureAlice S × mixtureBob S)
      (mixtureAlice S × mixtureBob S) ℂ) :
    (mixtureEmbedding S)ᴴ * E * mixtureEmbedding S =
      E.submatrix (mixtureMatchedIndex S) (mixtureMatchedIndex S) := by sorry
