-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalPieceWord_push_eq_regions
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalPieceWord_push_eq_regions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:29:45.010818+00:00
-- url     : https://prove2.me/theorems/7a16f139-629f-4dba-9c55-5307a78f3ab8
-- title:
--   BDL26 RXLocal Replacement: x Local Piece Word push eq regions
-- statement:
--   Region extension decomposes as its two grid words and two strip words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L1041-L1059
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L1041-L1059

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalPieceWord_push_eq_regions
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (syndrome : Word Field (DoubleCylinderFace P x S)) :
    xLocalWordPush (fun cell => xLocalPieceCellMap P x S (face, cell))
        (xLocalPieceWord P x S face syndrome) =
      xLocalWordPush (fun ij : GridVertex S.half => Sum.inl (0, face, ij))
        (xLocalLayerWord P x S syndrome face 0) +
      xLocalWordPush (fun ij : GridVertex S.half => Sum.inl (1, face, ij))
        (xLocalLayerWord P x S syndrome face 1) +
      xLocalWordPush (fun i : StripVertex S.half => Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face 0) i)) (xLocalStripWord P x S syndrome face 0) +
      xLocalWordPush (fun i : StripVertex S.half => Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face 1) i)) (xLocalStripWord P x S syndrome face 1) := by sorry
