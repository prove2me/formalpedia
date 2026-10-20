-- Prove2me | Theorems.Thm_QuantumParallelRepetition_sourceHistoryAcceptedMass_gt_of_greedy
-- name    : QuantumParallelRepetition.sourceHistoryAcceptedMass_gt_of_greedy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/08a647be-55fa-44cc-ad00-852e4b531e2f
-- title:
--   QuantumParallelRepetition.sourceHistoryAcceptedMass_gt_of_greedy
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
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.sourceHistoryAcceptedMass_gt_of_greedy
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    {η : ℝ}
    (hgreedy :
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i) <
        ((Finset.univ \ D).card : ℝ) *
          (η * (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent
              (repeatedCoordinateWin G n) D))) :
    (1 - η) *
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D) <
      sourceHistoryAcceptedMass G n S D := by sorry
