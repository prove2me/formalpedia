-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_radialGauge_strip_coboundary
-- name    : QEC.Coding.BDL26XLocalRadialParity.radialGauge_strip_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:32:38.316401+00:00
-- url     : https://prove2.me/theorems/6add60d3-487e-4c90-bb31-3c0fbb2aad5b
-- title:
--   BDL26 XLocal Radial Parity: radial Gauge strip coboundary
-- statement:
--   The BDL26 XLocal Radial Parity construction uses the radial Gauge strip coboundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L358-L370
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L358-L370

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.radialGauge_strip_coboundary
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (side : Two) (i : Fin S.half) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (radialGauge P A x S selected alpha)
      (Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) i)) = 0 := by sorry
