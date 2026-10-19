-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pureVectorStrategy_outcomeProbability
-- name    : QuantumParallelRepetition.pureVectorStrategy_outcomeProbability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/6e538ead-c62f-46f3-8845-1ee56152683a
-- title:
--   QuantumParallelRepetition.pureVectorStrategy_outcomeProbability
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.pureVectorStrategy_outcomeProbability
    {X Y A B : Type*} {dA dB : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB)
    (x : X) (y : Y) (a : A) (b : B) :
    (pureVectorStrategy G z hz PA PB).outcomeProbability x y a b =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := dA × dB) (𝕜 := ℂ)
          ((PA x).effect a ⊗ₖ (PB y).effect b)) z := by sorry
