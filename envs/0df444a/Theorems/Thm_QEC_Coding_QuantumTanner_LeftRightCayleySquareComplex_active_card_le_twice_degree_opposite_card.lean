-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_active_card_le_twice_degree_opposite_card
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.active_card_le_twice_degree_opposite_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:57:12.955997+00:00
-- url     : https://prove2.me/theorems/21770207-22bb-4dcc-8f33-485cfde7c79e
-- title:
--   Left Right Cayley Square Complex: active card le twice degree opposite card
-- statement:
--   Heavy coverage and a small exceptional fraction force the ambient active
--   set to be only linear in the opposite heavy set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavySelection.lean#L96-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavySelection.lean#L96-L117

import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_DegreeSelection
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.active_card_le_twice_degree_opposite_card
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (S exceptional : Finset G) (hExceptional : 2 * (S ∩ exceptional).card ≤ S.card)
    (hCoverage : (S \ exceptional).card ≤
      crossCount (X.heavyUnionGraph side x cutoff) (S \ exceptional)
        (X.oppositeHeavySet side x cutoff (S \ exceptional))) :
    S.card ≤ 2 * (Fintype.card A + Fintype.card B) *
      (X.oppositeHeavySet side x cutoff (S \ exceptional)).card := by sorry
