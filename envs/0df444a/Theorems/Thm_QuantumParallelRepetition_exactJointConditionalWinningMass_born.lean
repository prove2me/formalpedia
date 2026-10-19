-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactJointConditionalWinningMass_born
-- name    : QuantumParallelRepetition.exactJointConditionalWinningMass_born
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/87e0495f-b833-407b-a8f6-a5d8a77b7d4e
-- title:
--   QuantumParallelRepetition.exactJointConditionalWinningMass_born
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactJointConditionalWinningMass_born
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    exactJointConditionalWinningMass
        G n S D seed history aliceAnswer bobAnswer x y =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
            exactConditionalQuestionWeight
              G n D seed history x y xs ys *
            bornTracePairing S.state.matrix
              (conditionedAliceCoordinateEffect
                G n S D aliceAnswer xs seed.coordinate.val a)
              (conditionedBobCoordinateEffect
                G n S D bobAnswer ys seed.coordinate.val b)
        else 0 := by sorry
