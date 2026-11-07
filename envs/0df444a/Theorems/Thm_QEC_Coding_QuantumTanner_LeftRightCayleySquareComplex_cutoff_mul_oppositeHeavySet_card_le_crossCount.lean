-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_cutoff_mul_oppositeHeavySet_card_le_crossCount
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.cutoff_mul_oppositeHeavySet_card_le_crossCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:53:48.986517+00:00
-- url     : https://prove2.me/theorems/3f3281b7-0aa2-4f0c-b826-0e50eaf15537
-- title:
--   Left Right Cayley Square Complex: cutoff mul opposite Heavy Set card le cross Count
-- statement:
--   Sum the genuine support degrees over the actual opposite heavy set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L356-L363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L356-L363

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.cutoff_mul_oppositeHeavySet_card_le_crossCount
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G) :
    cutoff * (X.oppositeHeavySet side x cutoff normal).card ≤
      crossCount X.unionCayleyGraph (X.oppositeHeavySet side x cutoff normal)
        (X.activeVerticesOnSide side x) := by sorry
