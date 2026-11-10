-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_strip_parity_boundary
-- name    : QEC.Coding.BDL26XLocalRadialParity.strip_parity_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:32:59.151812+00:00
-- url     : https://prove2.me/theorems/5d9b76d2-8a3a-43c2-8473-2229e9d9a909
-- title:
--   BDL26 XLocal Radial Parity: strip parity boundary
-- statement:
--   Strip parity retains only the two copied arms and the original endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L155-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L155-L184

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.strip_parity_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : Word Field (DoubleCylinderEdge P x S))
    (face : XStarFace P x) (side : Two) :
    totalParity (xLocalStripWord P x S
      (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e) face side) =
      (∑ i : Fin S.half, e (Sum.inl (0,
        (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x face side) i).val))) +
      (∑ i : Fin S.half, e (Sum.inl (1,
        (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x face side) i).val))) +
      e (Sum.inr (subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeStart P x (xStarFaceBoundaryEdge P x face side)))) +
      e (Sum.inr (subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face side)))) := by sorry
