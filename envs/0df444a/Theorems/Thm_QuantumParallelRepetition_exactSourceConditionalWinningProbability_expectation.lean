-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactSourceConditionalWinningProbability_expectation
-- name    : QuantumParallelRepetition.exactSourceConditionalWinningProbability_expectation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:46.229074+00:00
-- url     : https://prove2.me/theorems/358bac63-266e-4589-bb7e-220242ee87d1
-- title:
--   QuantumParallelRepetition.exactSourceConditionalWinningProbability_expectation
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

theorem QuantumParallelRepetition.exactSourceConditionalWinningProbability_expectation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t) =
      ∑ q : ExactJointOutcome X Y A B D,
        if repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
        then exactPostselectedJointLaw G n S D q
        else 0 := by sorry
