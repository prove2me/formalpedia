-- Prove2me | Theorems.Thm_QuantumParallelRepetition_Strategy_winProbability_eq_winningEffect_born
-- name    : QuantumParallelRepetition.Strategy.winProbability_eq_winningEffect_born
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/901c597d-95e1-477e-8708-79fea5263aed
-- title:
--   QuantumParallelRepetition.Strategy.winProbability_eq_winningEffect_born
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open QuantumParallelRepetition.Strategy
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

theorem QuantumParallelRepetition.Strategy.winProbability_eq_winningEffect_born
    (S : Strategy G) :
    S.winProbability =
      ∑ x : X, ∑ y : Y,
        G.questionWeight x y *
          (Matrix.trace (S.state.matrix * S.winningEffect x y)).re := by sorry
