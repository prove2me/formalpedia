-- Prove2me | Theorems.Thm_QuantumParallelRepetition_repeatedStrategy_exists_divisor_greedy_conditioning
-- name    : QuantumParallelRepetition.repeatedStrategy_exists_divisor_greedy_conditioning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/d220d051-c573-4f95-aea1-eec0416a39b8
-- title:
--   QuantumParallelRepetition.repeatedStrategy_exists_divisor_greedy_conditioning
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
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.repeatedStrategy_exists_divisor_greedy_conditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {η : ℝ} {q : ℕ}
    (hη : 0 < η) (hη_one : η ≤ 1)
    (hq : 0 < q) (hqn : q ≤ n)
    (hwitness :
      Real.exp (-(η / (4 * (q : ℝ))) * (n : ℝ)) <
        S.winProbability) :
    ∃ D : Finset (Fin n),
      D.card < n / q ∧
      S.winProbability ≤
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D) ∧
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i)
        <
      ((Finset.univ \ D).card : ℝ) *
        (η * (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D)) := by sorry
