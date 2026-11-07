-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_mixing_of_cayley_bilinear_bounds
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.mixing_of_cayley_bilinear_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:56:33.557129+00:00
-- url     : https://prove2.me/theorems/3668ad86-6357-44b2-95e7-51a7f62e55c2
-- title:
--   Left Right Cayley Square Complex: mixing of cayley bilinear bounds
-- statement:
--   Actual Cayley spectral bounds imply mixing for the same-side square
--   graph and union graph, with exactly the unnormalized product/sum constants.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L188-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L188-L207

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.mixing_of_cayley_bilinear_bounds
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (lambda mu : ℝ) (hLambda : 0 ≤ lambda) (hMu : 0 ≤ mu)
    (hLeft : HasMeanZeroBilinearBound X.leftCayleyGraph lambda)
    (hRight : HasMeanZeroBilinearBound X.rightCayleyGraph mu) :
    (∀ side, HasExpanderMixingBound (X.squareGraph side)
      (Fintype.card A * Fintype.card B) (lambda * mu)) ∧
    HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) (lambda + mu) := by sorry
