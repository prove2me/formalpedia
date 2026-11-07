-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_normal_card_le_heavy_crossCount_of_covers
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.normal_card_le_heavy_crossCount_of_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:53:09.218294+00:00
-- url     : https://prove2.me/theorems/c930a2bf-86d9-4918-86a1-cbadaaee081b
-- title:
--   Left Right Cayley Square Complex: normal card le heavy cross Count of covers
-- statement:
--   Actual small covers force a heavy line at every normal active vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L400-L419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L400-L419

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.normal_card_le_heavy_crossCount_of_covers
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (dA dB : Nat)
    (hA : HasMinimumDistanceAtLeast CA dA) (hB : HasMinimumDistanceAtLeast CB dB)
    (hNormal : normal ⊆ X.activeVerticesOnSide side x)
    (hCovers : ∀ g ∈ normal, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (g, side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧
      cutoff + columns.card ≤ dB ∧ cutoff + rows.card ≤ dA) :
    normal.card ≤ crossCount (X.heavyUnionGraph side x cutoff) normal
      (X.oppositeHeavySet side x cutoff normal) := by sorry
