-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_layer_coboundary_apply
-- name    : QEC.Coding.BDL26XLocalRadialParity.layer_coboundary_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:32:02.820632+00:00
-- url     : https://prove2.me/theorems/8500bd12-18f5-4cff-a4ca-5521db4d5880
-- title:
--   BDL26 XLocal Radial Parity: layer coboundary apply
-- statement:
--   The actual copied-square coboundary is its four edge values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L41-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L41-L57

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.layer_coboundary_apply
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : Word Field (DoubleCylinderEdge P x S))
    (face : XStarFace P x) (copy : Two) (i j : Fin S.half) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e
        (Sum.inl (copy, face, i, j)) =
      e (Sum.inl (copy, subdivisionHorizontalEdge P x S face i j.castSucc)) +
      e (Sum.inl (copy, subdivisionVerticalEdge P x S face i.succ j)) +
      e (Sum.inl (copy, subdivisionHorizontalEdge P x S face i j.succ)) +
      e (Sum.inl (copy, subdivisionVerticalEdge P x S face i.castSucc j)) := by sorry
