-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactJointCoordinateFilter_born
-- name    : QuantumParallelRepetition.exactJointCoordinateFilter_born
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/de4f0db2-2619-478f-9f75-3941c350f3d3
-- title:
--   QuantumParallelRepetition.exactJointCoordinateFilter_born
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

theorem QuantumParallelRepetition.exactJointCoordinateFilter_born
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) (a : A) (b : B)
    (nonzero : exactFiberQuestionMass
      G n D seed history x y ≠ 0) :
    bornTracePairing S.state.matrix
        (exactJointAliceCoordinateFilter
          G n S D seed history aliceAnswer x y a)
        (exactJointBobCoordinateFilter
          G n S D seed history bobAnswer x y b) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        exactConditionalQuestionWeight
          G n D seed history x y xs ys *
        bornTracePairing S.state.matrix
          (conditionedAliceCoordinateEffect
            G n S D aliceAnswer xs seed.coordinate.val a)
          (conditionedBobCoordinateEffect
            G n S D bobAnswer ys seed.coordinate.val b) := by sorry
