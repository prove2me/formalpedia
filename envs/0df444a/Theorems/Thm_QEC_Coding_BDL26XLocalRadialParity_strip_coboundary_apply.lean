-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_strip_coboundary_apply
-- name    : QEC.Coding.BDL26XLocalRadialParity.strip_coboundary_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:32:19.962998+00:00
-- url     : https://prove2.me/theorems/d90c8f8b-a45c-48ba-9c2b-2bfc51d55b7f
-- title:
--   BDL26 XLocal Radial Parity: strip coboundary apply
-- statement:
--   The actual rectangle coboundary has two copied and two vertical sides.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L60-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L60-L77

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.strip_coboundary_apply
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : Word Field (DoubleCylinderEdge P x S))
    (edge : SubdivisionBoundaryEdge P x S) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e (Sum.inr edge) =
      e (Sum.inl (0, edge.val)) + e (Sum.inl (1, edge.val)) +
      e (Sum.inr (subdivisionBoundaryEdgeStart P x S edge)) +
      e (Sum.inr (subdivisionBoundaryEdgeEnd P x S edge)) := by sorry
