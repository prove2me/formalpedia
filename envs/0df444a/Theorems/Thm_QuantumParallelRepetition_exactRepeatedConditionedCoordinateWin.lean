-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactRepeatedConditionedCoordinateWin
-- name    : QuantumParallelRepetition.exactRepeatedConditionedCoordinateWin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/9998c42b-304d-4af0-8c53-6aa8614c9db6
-- title:
--   QuantumParallelRepetition.exactRepeatedConditionedCoordinateWin
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactRepeatedConditionedCoordinateWin
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : Fin n) :
    (∑ outcome : ExactOutcome X Y A B n,
      if repeatedCoordinateWin G n i outcome = true then
        repeatedConditionedOutcomeLaw G n S D outcome
      else 0) =
    (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) (insert i D)) /
        repeatedPostselectionMass G n S D := by sorry
