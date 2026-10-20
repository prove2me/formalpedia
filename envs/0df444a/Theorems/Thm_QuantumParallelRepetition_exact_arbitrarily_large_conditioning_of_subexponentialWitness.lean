-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exact_arbitrarily_large_conditioning_of_subexponentialWitness
-- name    : QuantumParallelRepetition.exact_arbitrarily_large_conditioning_of_subexponentialWitness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/f17d19a7-47e5-493c-a58d-b1c8dbb95265
-- title:
--   QuantumParallelRepetition.exact_arbitrarily_large_conditioning_of_subexponentialWitness
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

theorem QuantumParallelRepetition.exact_arbitrarily_large_conditioning_of_subexponentialWitness
    (G : Game X Y A B)
    (witness : HasSubexponentialWitness (repeatedEntangledValue G))
    {failureTolerance rateTolerance : ℝ}
    (failure_positive : 0 < failureTolerance)
    (failure_at_most_one : failureTolerance ≤ 1)
    (rate_positive : 0 < rateTolerance)
    (lower : ℕ) :
    ∃ n : ℕ, lower < n ∧
      ∃ S : Strategy (G.repeat n),
        ∃ D : Finset (Fin n),
          0 < S.winProbability ∧
          0 < repeatedPostselectionMass G n S D ∧
          0 < (Finset.univ \ D).card ∧
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D < failureTolerance ∧
          martingaleRate G n S D ≤
            rateTolerance ^ 2 / 8 ∧
          exactSourcePinskerRate G n S D ≤
            rateTolerance / 2 := by sorry
