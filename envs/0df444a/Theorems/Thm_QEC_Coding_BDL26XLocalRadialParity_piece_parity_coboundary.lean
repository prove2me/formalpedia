-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_piece_parity_coboundary
-- name    : QEC.Coding.BDL26XLocalRadialParity.piece_parity_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:34:17.429849+00:00
-- url     : https://prove2.me/theorems/30163754-b46e-4f51-b317-f6bcc02c2169
-- title:
--   BDL26 XLocal Radial Parity: piece parity coboundary
-- statement:
--   Every genuine coboundary has the source's link-graph piece parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L234-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L234-L255

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.piece_parity_coboundary
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : Word Field (DoubleCylinderEdge P x S))
    (face : XStarFace P x) :
    (∑ region : Two ⊕ Two, xLocalRegionParity P x S
      (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e) face region) =
      interfaceParity P A x S e (faceNeighbor P x face 0) +
      interfaceParity P A x S e (faceNeighbor P x face 1) := by sorry
