-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_zeroSet_diff_523cff7b1a84
-- name    : P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_zeroSet_diff_523cff7b1a84
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:49.399976+00:00
-- url     : https://prove2.me/theorems/9b8298c9-bb3a-4da6-b10b-87a742d2b3ed
-- title:
--   P2 M Ground Theory Heights  Heights Chart Change measurable Set zero Set diff 523cff7b1a84: P2 M Ground Theory Heights  Heights Chart Change measurable Set zero Set diff 523cff7b1a84
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Change measurable Set zero Set diff 523cff7b1a84 construction uses the P2 M Ground Theory Heights  Heights Chart Change measurable Set zero Set diff 523cff7b1a84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L25-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntChartChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChange
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_zeroSet_diff_523cff7b1a84 (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) :
    MeasurableSet (zeroSet J \ {x | linEval u x = 0}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChange».«measurableSet_zeroSet_diff» := P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_zeroSet_diff_523cff7b1a84
