-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_otherIncidentVertices_card
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.otherIncidentVertices_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:41:35.978731+00:00
-- url     : https://prove2.me/theorems/1c6446c9-fdb8-42f8-8a97-4f4f8df09bc6
-- title:
--   Left Right Cayley Square Complex: other Incident Vertices card
-- statement:
--   Every incident square has precisely one other endpoint on the same side.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L52-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L52-L64

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.otherIncidentVertices_card
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool) (g : G) (q : Square)
    (hg : X.Incident (g, side) q) :
    (Finset.univ.filter fun h => X.Incident (h, side) q ∧ g ≠ h).card = 1 := by sorry
