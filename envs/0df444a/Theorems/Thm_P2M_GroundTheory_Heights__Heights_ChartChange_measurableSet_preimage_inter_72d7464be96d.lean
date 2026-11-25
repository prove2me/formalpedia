-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_preimage_inter_72d7464be96d
-- name    : P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_preimage_inter_72d7464be96d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:06.260454+00:00
-- url     : https://prove2.me/theorems/c4acb1bc-94f4-4124-88a5-6c1d5533b2ab
-- title:
--   P2 M Ground Theory Heights  Heights Chart Change measurable Set preimage inter 72d7464be96d: P2 M Ground Theory Heights  Heights Chart Change measurable Set preimage inter 72d7464be96d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Change measurable Set preimage inter 72d7464be96d construction uses the P2 M Ground Theory Heights  Heights Chart Change measurable Set preimage inter 72d7464be96d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L29-L44

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

theorem P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_preimage_inter_72d7464be96d {Ψ : (Fin n → ℂ) → Fin n → ℂ} {U S E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hΨ : ContinuousOn Ψ U) (hSU : S ⊆ U) (hS : MeasurableSet S)
    (hE : MeasurableSet E) : MeasurableSet (Ψ ⁻¹' E ∩ S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChange».«measurableSet_preimage_inter» := P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_preimage_inter_72d7464be96d
