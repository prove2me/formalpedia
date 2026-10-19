-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pureVectorWinningProbability_eq
-- name    : QuantumParallelRepetition.pureVectorWinningProbability_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/f931b21d-a56d-4f69-805c-fbcb7171374e
-- title:
--   QuantumParallelRepetition.pureVectorWinningProbability_eq
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]

theorem QuantumParallelRepetition.pureVectorWinningProbability_eq
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB) :
    (pureVectorStrategy G z hz PA PB).winProbability =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := dA × dB) (𝕜 := ℂ)
            (pureVerifierEffect G z hz PA PB x y)) z := by sorry
