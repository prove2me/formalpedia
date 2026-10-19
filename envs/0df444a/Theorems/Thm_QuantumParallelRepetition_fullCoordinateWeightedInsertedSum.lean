-- Prove2me | Theorems.Thm_QuantumParallelRepetition_fullCoordinateWeightedInsertedSum
-- name    : QuantumParallelRepetition.fullCoordinateWeightedInsertedSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/5e0e57ec-0f6b-4ca9-a5ef-25b9d8beb939
-- title:
--   QuantumParallelRepetition.fullCoordinateWeightedInsertedSum
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
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.fullCoordinateWeightedInsertedSum
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D)
    (value : (h : FullSubsetHistory X Y n (insert i D) L) →
      ({j : Fin n // j ∈ insert i D} → A) →
      ({j : Fin n // j ∈ insert i D} → B) → ℝ) :
    (∑ h : FullSubsetHistory X Y n (insert i D) L,
      ∑ α : {j : Fin n // j ∈ insert i D} → A,
      ∑ β : {j : Fin n // j ∈ insert i D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          value h α β) =
      ∑ r : FullCoordinateRevealHistory X Y n D L i,
      ∑ α : {j : Fin n // j ∈ D} → A,
      ∑ β : {j : Fin n // j ∈ D} → B,
        fullCoordinateBaseWeight G D L i r *
          fullCoordinateBaseWinIndicator G D L i r α β *
          (∑ x : X, ∑ y : Y, G.questionWeight x y *
            (∑ a : A, ∑ b : B,
              (if G.predicate x y a b = true then 1 else 0) *
                value (fullCoordinateInsertedHistory D L i r x y)
                  (fullCoordinateAnswerExtension D i α a)
                  (fullCoordinateAnswerExtension D i β b))) := by sorry
