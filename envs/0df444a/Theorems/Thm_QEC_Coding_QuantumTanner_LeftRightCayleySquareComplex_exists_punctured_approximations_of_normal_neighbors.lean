-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_punctured_approximations_of_normal_neighbors
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_punctured_approximations_of_normal_neighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:57:03.406199+00:00
-- url     : https://prove2.me/theorems/0e17860f-d6d1-4cf9-9fe2-d56cd46f3855
-- title:
--   Left Right Cayley Square Complex: exists punctured approximations of normal neighbors
-- statement:
--   Normal covers at left/right neighbors produce the actual close
--   punctured row/column words, with the source's sum-of-line-errors budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L32-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean#L32-L75

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_punctured_approximations_of_normal_neighbors
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB : Nat) (hA : HasMinimumDistanceAtLeast CA dA)
    (hB : HasMinimumDistanceAtLeast CB dB)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool)
    (removedA : Finset A) (removedB : Finset B) (rowError columnError : Nat)
    (hLeft : ∀ a : KeptCoordinate removedA, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (X.leftGenerator a.1 * g, !side) x ∈
        (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (X.leftGenerator a.1 * g, !side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧ columns.card ≤ rowError)
    (hRight : ∀ b : KeptCoordinate removedB, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (g * X.rightGenerator b.1, !side) x ∈
        (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (g * X.rightGenerator b.1, !side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧ rows.card ≤ columnError) :
    ∃ C R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB),
      C ∈ (columnCode (puncturedCode CA removedA)).carrier ∧
      R ∈ (rowCode (puncturedCode CB removedB)).carrier ∧
      HammingWeight (tensorPunctureMap removedA removedB (X.localRestriction (g, side) x) + C) ≤
        Fintype.card B * columnError ∧
      HammingWeight (tensorPunctureMap removedA removedB (X.localRestriction (g, side) x) + R) ≤
        Fintype.card A * rowError := by sorry
