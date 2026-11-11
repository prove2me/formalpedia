-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_boundary_other_x
-- name    : QEC.Coding.BDL26RXXStarTransport.potential_boundary_other_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:10:29.777106+00:00
-- url     : https://prove2.me/theorems/7de1ea1d-4dac-47c3-95c6-140f7c77ff5c
-- title:
--   BDL26 RXXStar Transport: potential boundary other x
-- statement:
--   The BDL26 RXXStar Transport construction uses the potential boundary other x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L203-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L203-L206

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.potential_boundary_other_x (x y : XCoord S i) (hy : y≠x) (a b : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y)
      ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b))=0 := by sorry
