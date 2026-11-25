-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ratioMap_dehom_40661f9296d6
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ratioMap_dehom_40661f9296d6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:05:24.292097+00:00
-- url     : https://prove2.me/theorems/d5a76e3c-5427-5955-827e-3cc63fc2db2e
-- title:
--   P2 M Ground Theory Heights  Heights Targets ratio Map dehom 40661f9296d6: P2 M Ground Theory Heights  Heights Targets ratio Map dehom 40661f9296d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets ratio Map dehom 40661f9296d6 construction uses the P2 M Ground Theory Heights  Heights Targets ratio Map dehom 40661f9296d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L50-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_Targets_ratioMap_dehom_40661f9296d6 (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    ratioMap i (dehom i f) = coneRatio i f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ratioMap_dehom» := P2M_GroundTheory_Heights__Heights_Targets_ratioMap_dehom_40661f9296d6
