-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_strip_cleanup
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_strip_cleanup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:27:30.364952+00:00
-- url     : https://prove2.me/theorems/055b0f5f-632a-42d2-9eec-65b4c4b481a8
-- title:
--   BDL26 RXLocal Replacement: x Local strip cleanup
-- statement:
--   Strip syndrome cleanup uses concrete internal vertical edges and no output budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L686-L701
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L686-L701

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_strip_cleanup
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (side : Two)
    (root : StripVertex S.half) (syndrome : Word Field (StripVertex S.half)) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f =
        xLocalWordPush (fun i : StripVertex S.half => Sum.inr
          (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x face side) i))
          (syndrome + Pi.single root (totalParity syndrome)) ∧
      connectingWeight P A x S f = 0 := by sorry
