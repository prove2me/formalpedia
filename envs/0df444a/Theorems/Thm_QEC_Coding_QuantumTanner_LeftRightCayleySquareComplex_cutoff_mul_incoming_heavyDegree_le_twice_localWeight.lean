-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_cutoff_mul_incoming_heavyDegree_le_twice_localWeight
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.cutoff_mul_incoming_heavyDegree_le_twice_localWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:53:01.849983+00:00
-- url     : https://prove2.me/theorems/c9c13664-c131-420d-90ef-0c47fc4bb724
-- title:
--   Left Right Cayley Square Complex: cutoff mul incoming heavy Degree le twice local Weight
-- statement:
--   The incoming heavy edges from any selected set give the same weight lower
--   bound after actual link rebasing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L299-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L299-L311

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.cutoff_mul_incoming_heavyDegree_le_twice_localWeight
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G) (h : G) :
    cutoff * (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h) ≤
      2 * HammingWeight (X.localRestriction (h, !side) x) := by sorry
