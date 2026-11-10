-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_even_pieces_cleanup
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_even_pieces_cleanup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:29:27.137861+00:00
-- url     : https://prove2.me/theorems/a4baf8ca-f4e4-49ac-b94c-740fbaa93e9b
-- title:
--   BDL26 RXLocal Replacement: x Local even pieces cleanup
-- statement:
--   A syndrome even on every face piece has a concrete correction bounded by
--   the sum of its four-region crossing budgets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L1133-L1155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L1133-L1155

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_even_pieces_cleanup
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (syndrome : Word Field (DoubleCylinderFace P x S))
    (heven : ∀ face : XStarFace P x,
      xLocalRegionParity P x S syndrome face (Sum.inl 0) +
      xLocalRegionParity P x S syndrome face (Sum.inl 1) +
      xLocalRegionParity P x S syndrome face (Sum.inr 0) +
      xLocalRegionParity P x S syndrome face (Sum.inr 1) = 0) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f = syndrome ∧
      connectingWeight P A x S f ≤ ∑ face : XStarFace P x, pieceCrossingCost
        (xLocalRegionParity P x S syndrome face (Sum.inl 0))
        (xLocalRegionParity P x S syndrome face (Sum.inl 1))
        (xLocalRegionParity P x S syndrome face (Sum.inr 0))
        (xLocalRegionParity P x S syndrome face (Sum.inr 1)) := by sorry
