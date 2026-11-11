-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_chart_incidence
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.chart_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:13:38.048539+00:00
-- url     : https://prove2.me/theorems/e4b814dc-a648-49d6-a3f4-4fe7b735595b
-- title:
--   BDL26 RXPhysical Star Transport: chart incidence
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the chart incidence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L500-L504
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L500-L504

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.chart_incidence (r : RX0 (state S i.val).presentation S)
    (p : RX1 (state S i.val).presentation S) :
    (state S (i.val+1)).presentation.xq (rxDegreeZeroEquiv S depth i h r)
      (upperQChart S depth i h p)=rxXQIncidence (state S i.val).presentation S r p := by sorry
