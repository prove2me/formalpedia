-- Prove2me | Theorems.Thm_QuantumParallelRepetition_mixtureJointEffect_compress
-- name    : QuantumParallelRepetition.mixtureJointEffect_compress
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/7fd21c74-d23e-494a-a3df-ac93c45d3c9f
-- title:
--   QuantumParallelRepetition.mixtureJointEffect_compress
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

theorem QuantumParallelRepetition.mixtureJointEffect_compress (S : J → Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    (((mixtureAlicePOVM S x).effect a ⊗ₖ
      (mixtureBobPOVM S y).effect b).submatrix
        (mixtureMatchedIndex S) (mixtureMatchedIndex S)) =
      Matrix.blockDiagonal' fun j =>
        (S j).jointEffect x y a b := by sorry
