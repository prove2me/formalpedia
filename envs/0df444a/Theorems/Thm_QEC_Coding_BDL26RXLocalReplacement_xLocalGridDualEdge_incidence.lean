-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalGridDualEdge_incidence
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalGridDualEdge_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:27:34.112599+00:00
-- url     : https://prove2.me/theorems/35e2b51a-13ef-411b-95de-8e27b967b1fc
-- title:
--   BDL26 RXLocal Replacement: x Local Grid Dual Edge incidence
-- statement:
--   The concrete interior grid dual edge affects exactly its two mapped cells.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L372-L399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L372-L399

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalGridDualEdge_incidence
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy : Two) (edge : GridEdge S.half)
    (target : DoubleCylinderFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S (xLocalGridDualEdge P x S face copy edge) target =
      (if target = Sum.inl (copy, face, gridStart S.half edge) then 1 else 0) +
        (if target = Sum.inl (copy, face, gridEnd S.half edge) then 1 else 0) := by sorry
