-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourcePhysicalStopBorn_eq_raw
-- name    : QuantumParallelRepetition.unconditionalActualFairSourcePhysicalStopBorn_eq_raw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:50.637979+00:00
-- url     : https://prove2.me/theorems/05c81412-f8c4-40eb-9610-609f0cd56758
-- title:
--   QuantumParallelRepetition.unconditionalActualFairSourcePhysicalStopBorn_eq_raw
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
open QuantumParallelRepetition.ClassicalSampling

theorem QuantumParallelRepetition.unconditionalActualFairSourcePhysicalStopBorn_eq_raw
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) (j : Fin L) :
    let d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
    let PA := unconditionalActualFairSourceAliceFlagPOVM
      G n S D denominator numerator nonempty a₀ P N L m flag
    let PB := unconditionalActualFairSourceBobFlagPOVM
      G n S D denominator numerator nonempty b₀ P N L m flag
    let stopped := actualStoppingBranchVector
      (actualStoppingQuestionLocalAction
        (unconditionalActualFairSourceAliceStoppingUnitary
          (P := P) (N := N) (L := L) (m := m)
          G n S D denominator numerator nonempty
          Q width schedule UA flag x)
        (unconditionalActualFairSourceBobStoppingUnitary
          (P := P) (N := N) (L := L) (m := m)
          G n S D denominator numerator nonempty
          Q width schedule UB flag y)
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          1 P N d L m)) j.succ j.succ
    unconditionalActualFairSourcePhysicalStopBorn
        G n S D denominator numerator nonempty a₀ b₀
        Q width schedule UA UB flag x y j =
      unconditionalActualC485RawPhysicalVerifierBorn
        G (PA j.succ x) (PB j.succ y) x y stopped := by sorry
