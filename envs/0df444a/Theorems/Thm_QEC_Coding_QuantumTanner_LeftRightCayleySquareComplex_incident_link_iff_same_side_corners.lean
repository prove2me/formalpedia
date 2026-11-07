-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_incident_link_iff_same_side_corners
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.incident_link_iff_same_side_corners
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:54:51.907469+00:00
-- url     : https://prove2.me/theorems/aa3bc4c8-ca57-46e1-8499-d4e4afda1727
-- title:
--   Left Right Cayley Square Complex: incident link iff same side corners
-- statement:
--   The two known corners exhaust all same-side incidences, by the actual
--   two-incidence law and TNC.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L46-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L46-L67

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.incident_link_iff_same_side_corners
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (g h : G) (side : Bool) (a : A) (b : B) :
    X.Incident (h, side) (X.link (g, side) (a, b)) ↔
      h = g ∨ h = X.leftGenerator a * g * X.rightGenerator b := by sorry
