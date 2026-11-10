-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalGridDualEdge_connectingWeight_zero
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalGridDualEdge_connectingWeight_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:26:21.423327+00:00
-- url     : https://prove2.me/theorems/c77d2c90-486a-4d78-a258-90aa8534a141
-- title:
--   BDL26 RXLocal Replacement: x Local Grid Dual Edge connecting Weight zero
-- statement:
--   Interior dual-grid corrections have no X-to-Q output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L519-L535
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L519-L535

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalGridDualEdge_connectingWeight_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (copy : Two)
    (correction : Word Field (GridEdge S.half)) :
    connectingWeight P A x S
      (xLocalWordPush (xLocalGridDualEdge P x S face copy) correction) = 0 := by sorry
