-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalGridDualEdge_coboundary
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalGridDualEdge_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:26:08.567368+00:00
-- url     : https://prove2.me/theorems/f97b7cb6-6329-48d6-93a9-ec8d2cebfb88
-- title:
--   BDL26 RXLocal Replacement: x Local Grid Dual Edge coboundary
-- statement:
--   Every actual dual-grid basis correction has its two-cell endpoint syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L471-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L471-L480

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalGridDualEdge_coboundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy : Two) (edge : GridEdge S.half) (b : Field) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (Pi.single (xLocalGridDualEdge P x S face copy edge) b) =
      Pi.single (Sum.inl (copy, face, gridStart S.half edge)) b +
        Pi.single (Sum.inl (copy, face, gridEnd S.half edge)) b := by sorry
