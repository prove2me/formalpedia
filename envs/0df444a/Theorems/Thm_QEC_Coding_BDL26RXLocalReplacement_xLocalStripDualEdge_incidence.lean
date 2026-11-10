-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalStripDualEdge_incidence
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalStripDualEdge_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:27:37.367196+00:00
-- url     : https://prove2.me/theorems/cdc858aa-4f0f-4312-97b0-afb811ff4c78
-- title:
--   BDL26 RXLocal Replacement: x Local Strip Dual Edge incidence
-- statement:
--   A strip-interior dual edge affects exactly its two adjacent rectangles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L616-L641
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L616-L641

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalStripDualEdge_incidence
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (side : Two) (i : StripEdge S.half)
    (target : DoubleCylinderFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S (xLocalStripDualEdge P x S face side i) target =
      (if target = Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (stripStart S.half i)) then 1 else 0) +
      (if target = Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (stripEnd S.half i)) then 1 else 0) := by sorry
