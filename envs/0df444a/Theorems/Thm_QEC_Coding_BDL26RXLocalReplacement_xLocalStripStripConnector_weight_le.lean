-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalStripStripConnector_weight_le
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalStripStripConnector_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:28:10.620438+00:00
-- url     : https://prove2.me/theorems/f4ff29a8-5400-4f25-a5ad-9106979d909e
-- title:
--   BDL26 RXLocal Replacement: x Local Strip Strip Connector weight le
-- statement:
--   The vertical old-Z connector contributes at most two output bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L850-L856
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L850-L856

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalStripStripConnector_weight_le
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (b : Field) :
    connectingWeight P A x S (Pi.single (xLocalStripStripConnector P x S face) b) ≤
      2 * bitWeight b := by sorry
