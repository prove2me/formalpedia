-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalStripDualEdge_connectingWeight_zero
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalStripDualEdge_connectingWeight_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:27:24.822141+00:00
-- url     : https://prove2.me/theorems/ab93143b-0b28-42a1-9ff7-70bfa3056f98
-- title:
--   BDL26 RXLocal Replacement: x Local Strip Dual Edge connecting Weight zero
-- statement:
--   Strip-interior corrections have zero actual X-to-Q weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L669-L683
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L669-L683

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalStripDualEdge_connectingWeight_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (side : Two)
    (correction : Word Field (StripEdge S.half)) :
    connectingWeight P A x S
      (xLocalWordPush (xLocalStripDualEdge P x S face side) correction) = 0 := by sorry
