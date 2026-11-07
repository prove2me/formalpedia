-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_normal_card_le_heavy_crossCount
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.normal_card_le_heavy_crossCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:54:05.671802+00:00
-- url     : https://prove2.me/theorems/4be96221-5a44-4739-9c3a-648fec88071d
-- title:
--   Left Right Cayley Square Complex: normal card le heavy cross Count
-- statement:
--   Every vertex with a heavy line contributes an actual edge into the
--   opposite heavy set, so the normal set is counted by heavy incidences.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L367-L397
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L367-L397

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.normal_card_le_heavy_crossCount
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (hHeavy : ∀ g ∈ normal,
      (∃ a, cutoff ≤ HammingWeight (rowRestriction a (X.localRestriction (g, side) x))) ∨
        ∃ b, cutoff ≤ HammingWeight (columnRestriction b (X.localRestriction (g, side) x))) :
    normal.card ≤ crossCount (X.heavyUnionGraph side x cutoff) normal
      (X.oppositeHeavySet side x cutoff normal) := by sorry
