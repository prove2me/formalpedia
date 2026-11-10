-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_piece_cleanup
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_piece_cleanup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:29:14.461018+00:00
-- url     : https://prove2.me/theorems/fda39134-1d43-4b7b-91a1-d024fa163bda
-- title:
--   BDL26 RXLocal Replacement: x Local piece cleanup
-- statement:
--   Each even-parity piece has a concrete correction with the exact crossing budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L1062-L1113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L1062-L1113

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_piece_cleanup
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (face : XStarFace P x)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (heven : xLocalRegionParity P x S syndrome face (Sum.inl 0) +
      xLocalRegionParity P x S syndrome face (Sum.inl 1) +
      xLocalRegionParity P x S syndrome face (Sum.inr 0) +
      xLocalRegionParity P x S syndrome face (Sum.inr 1) = 0) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f =
        xLocalWordPush (fun cell => xLocalPieceCellMap P x S (face, cell))
          (xLocalPieceWord P x S face syndrome) ∧
      connectingWeight P A x S f ≤ pieceCrossingCost
        (xLocalRegionParity P x S syndrome face (Sum.inl 0))
        (xLocalRegionParity P x S syndrome face (Sum.inl 1))
        (xLocalRegionParity P x S syndrome face (Sum.inr 0))
        (xLocalRegionParity P x S syndrome face (Sum.inr 1)) := by sorry
