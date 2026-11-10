-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_radialGauge_layer_coboundary
-- name    : QEC.Coding.BDL26XLocalRadialParity.radialGauge_layer_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:31:24.769706+00:00
-- url     : https://prove2.me/theorems/6376d006-f8ec-46ef-bf5b-58580e777ee6
-- title:
--   BDL26 XLocal Radial Parity: radial Gauge layer coboundary
-- statement:
--   The gauge changes only the origin square in the selected layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L345-L356
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L345-L356

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.radialGauge_layer_coboundary
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (copy : Two) (i j : Fin S.half) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (radialGauge P A x S selected alpha) (Sum.inl (copy, face, i, j)) =
      if copy = selected ∧ i.val = 0 ∧ j.val = 0 then
        alpha (faceNeighbor P x face 0) + alpha (faceNeighbor P x face 1) else 0 := by sorry
