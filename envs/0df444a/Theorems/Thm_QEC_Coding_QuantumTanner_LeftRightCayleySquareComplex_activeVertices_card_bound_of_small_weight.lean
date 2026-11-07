-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_activeVertices_card_bound_of_small_weight
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.activeVertices_card_bound_of_small_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:59:15.775701+00:00
-- url     : https://prove2.me/theorems/3849ea21-daa7-4b92-b58a-e7b0c084867a
-- title:
--   Left Right Cayley Square Complex: active Vertices card bound of small weight
-- statement:
--   The source's global weight threshold implies its active-set bound, using
--   the actual incidence count and the minimum-distance bound for dual tensors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExpandingDistance.lean#L26-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExpandingDistance.lean#L26-L67

import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.activeVertices_card_bound_of_small_weight
    (X : LeftRightCayleySquareComplex G A B Square)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB Delta : Nat) (delta epsilon : ℝ)
    (hDelta : 0 < Delta) (hDeltaDistance : 0 < delta)
    (hCardA : Fintype.card A = Delta) (hCardB : Fintype.card B = Delta)
    (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hDistanceA : delta * Delta ≤ (dA : ℝ)) (hDistanceB : delta * Delta ≤ (dB : ℝ))
    (side : Bool) (x : Word (ZMod 2) Square)
    (hLocal : ∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier)
    (hWeight : (HammingWeight x : ℝ) <
      delta * Fintype.card Square / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon))) :
    ((X.activeVerticesOnSide side x).card : ℝ) ≤
      Fintype.card G / (4 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) := by sorry
