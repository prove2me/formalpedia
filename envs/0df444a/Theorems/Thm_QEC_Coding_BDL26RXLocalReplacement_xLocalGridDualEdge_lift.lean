-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalGridDualEdge_lift
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalGridDualEdge_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:26:22.266715+00:00
-- url     : https://prove2.me/theorems/339d4a17-434f-4fdb-bb72-2676355d9af5
-- title:
--   BDL26 RXLocal Replacement: x Local Grid Dual Edge lift
-- statement:
--   Internal grid corrections commute with the actual X-local degree-one map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L483-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L483-L490

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalGridDualEdge_lift
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy : Two) :
    (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)).comp
        (xLocalWordPush (xLocalGridDualEdge P x S face copy)) =
      (xLocalWordPush (fun ij : GridVertex S.half => Sum.inl (copy, face, ij))).comp
        (graphBoundary (gridStart S.half) (gridEnd S.half)) := by sorry
