-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_parent_computed
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.parent_computed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:12:26.054476+00:00
-- url     : https://prove2.me/theorems/2985886e-c6b7-4544-bf90-b557ce103847
-- title:
--   BDL26 RXPhysical Star Transport: parent computed
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the parent computed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L132-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L132-L135

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.parent_computed (u : FamilyX S depth i.succ) :
    parent S (i.val+1) (Vertex.x u)=some (Vertex.x (parentX S depth i h u)) := by sorry
