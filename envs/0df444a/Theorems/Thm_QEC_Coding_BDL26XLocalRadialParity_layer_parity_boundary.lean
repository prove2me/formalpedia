-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_layer_parity_boundary
-- name    : QEC.Coding.BDL26XLocalRadialParity.layer_parity_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:32:45.709075+00:00
-- url     : https://prove2.me/theorems/317dc467-a1ca-4f9c-8392-2b968ad99125
-- title:
--   BDL26 XLocal Radial Parity: layer parity boundary
-- statement:
--   Summing a copied grid cancels all internal edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L80-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L80-L117

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.layer_parity_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : Word Field (DoubleCylinderEdge P x S))
    (face : XStarFace P x) (copy : Two) :
    totalParity (xLocalLayerWord P x S
      (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e) face copy) =
      (∑ i : Fin S.half,
        e (Sum.inl (copy, subdivisionHorizontalEdge P x S face i 0))) +
      (∑ i : Fin S.half,
        e (Sum.inl (copy, subdivisionHorizontalEdge P x S face i (Fin.last S.half)))) +
      (∑ j : Fin S.half,
        e (Sum.inl (copy, subdivisionVerticalEdge P x S face 0 j))) +
      (∑ j : Fin S.half,
        e (Sum.inl (copy, subdivisionVerticalEdge P x S face (Fin.last S.half) j))) := by sorry
