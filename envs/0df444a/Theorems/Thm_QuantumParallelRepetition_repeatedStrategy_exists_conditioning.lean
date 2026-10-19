-- Prove2me | Theorems.Thm_QuantumParallelRepetition_repeatedStrategy_exists_conditioning
-- name    : QuantumParallelRepetition.repeatedStrategy_exists_conditioning
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/edbcadff-efa7-4b47-8fc9-ab62a8ddd88c
-- title:
--   QuantumParallelRepetition.repeatedStrategy_exists_conditioning
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

theorem QuantumParallelRepetition.repeatedStrategy_exists_conditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {η : ℝ} {q : ℕ}
    (hwin : 0 < S.winProbability)
    (hη : 0 < η) (hη_one : η ≤ 1)
    (hq : q ≤ n)
    (hterminal : (1 - η) ^ q < S.winProbability) :
    ∃ C : Finset (Fin n),
      C.card < q ∧
      S.winProbability ≤ repeatedPostselectionMass G n S C ∧
      0 < repeatedPostselectionMass G n S C ∧
      0 < (Finset.univ \ C).card ∧
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) C < η := by sorry
