-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalPieceWord_sum_push
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalPieceWord_sum_push
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:29:30.964242+00:00
-- url     : https://prove2.me/theorems/fb0cefb9-f771-4123-97d7-6657158b0fef
-- title:
--   BDL26 RXLocal Replacement: x Local Piece Word sum push
-- statement:
--   Reassembling every disjoint piece recovers the original syndrome exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L1116-L1129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L1116-L1129

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalPieceWord_sum_push
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S)) :
    (∑ face : XStarFace P x,
      xLocalWordPush (fun cell => xLocalPieceCellMap P x S (face, cell))
        (xLocalPieceWord P x S face syndrome)) = syndrome := by sorry
