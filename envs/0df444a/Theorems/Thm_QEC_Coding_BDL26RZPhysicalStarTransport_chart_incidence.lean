-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_chart_incidence
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.chart_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:41:29.925403+00:00
-- url     : https://prove2.me/theorems/d50f6767-62ab-40ab-869f-ad7619494ad8
-- title:
--   BDL26 RZPhysical Star Transport: chart incidence
-- statement:
--   The BDL26 RZPhysical Star Transport construction uses the chart incidence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L160-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L160-L165

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

theorem QEC.Coding.BDL26RZPhysicalStarTransport.chart_incidence (q : RZQ (Old S depth i) S) (z : RZZ (Old S depth i) S) :
    (state S (i.val+1)).presentation.qz
      (upperQChart S depth i odd q) (upperZChart S depth i odd z)=
      rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S q z := by sorry
