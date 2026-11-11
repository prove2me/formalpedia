-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_boundaryCenter_basis
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:35:26.683638+00:00
-- url     : https://prove2.me/theorems/4e8d87e7-5e9c-4a80-bcf1-7d0bc158d710
-- title:
--   BDL26 RXPhysical Star Transport: boundary Center basis
-- statement:
--   Its global singleton is exactly the lift of the explicit nonzero vertical-gradient witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L433-L436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L433-L436

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_basis (x : XCoord S i) :
    canonicalBasisWord (boundaryCenter S depth i h x)=
      (rxContract S depth i h).support_decomposition.cxLift0 x (boundarySingleton S depth i x) := by sorry
