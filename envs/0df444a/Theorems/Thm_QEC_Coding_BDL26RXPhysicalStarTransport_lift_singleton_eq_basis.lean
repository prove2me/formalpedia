-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lift_singleton_eq_basis
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.lift_singleton_eq_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:21:23.075808+00:00
-- url     : https://prove2.me/theorems/2dde9069-c6ab-42b9-8e57-2a31867b6cb4
-- title:
--   BDL26 RXPhysical Star Transport: lift singleton eq basis
-- statement:
--   The lifted local singleton is exactly the global basis at its actual X chart coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L100-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L100-L123

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.lift_singleton_eq_basis (x : XCoord S i)
    (v : DoubleCylinderVertex (state S i.val).presentation x S) :
    (rxContract S depth i h).support_decomposition.cxLift0 x (Pi.single v 1) =
      canonicalBasisWord (rxDegreeZeroEquiv S depth i h ⟨x,v⟩) := by sorry
