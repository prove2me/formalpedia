-- Prove2me | Theorems.Thm_QuantumParallelRepetition_actualStoppingQuestionLocalWinningEffect_quadratic
-- name    : QuantumParallelRepetition.actualStoppingQuestionLocalWinningEffect_quadratic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/f4664b28-0b20-4fd0-b658-a2eaf9646995
-- title:
--   QuantumParallelRepetition.actualStoppingQuestionLocalWinningEffect_quadratic
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]

theorem QuantumParallelRepetition.actualStoppingQuestionLocalWinningEffect_quadratic
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (r : R) → Y → POVM B (ι r))
    (U : X → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (V : Y → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r)))
    (normalized : ‖z‖ = 1)
    (x : X) (y : Y) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
        (pureVerifierEffect G z normalized
          (fun x => unitaryConjugatePOVM (U x)
            (dependentBlockPOVM (fun r => PA r x)))
          (fun y => unitaryConjugatePOVM (V y)
            (dependentBlockPOVM (fun r => PB r y)))
          x y)) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
          (actualStoppingGlobalWinningEffect
            G PA PB x y))
        (actualStoppingQuestionLocalAction
          (U x) (V y) z) := by sorry
