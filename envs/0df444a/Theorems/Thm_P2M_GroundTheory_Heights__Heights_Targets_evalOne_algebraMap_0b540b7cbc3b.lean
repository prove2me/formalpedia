-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_evalOne_algebraMap_0b540b7cbc3b
-- name    : P2M_GroundTheory_Heights__Heights_Targets_evalOne_algebraMap_0b540b7cbc3b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:26.23492+00:00
-- url     : https://prove2.me/theorems/8b2cdf62-8468-58e5-a57c-307cfc3220bf
-- title:
--   P2 M Ground Theory Heights  Heights Targets eval One algebra Map 0b540b7cbc3b: P2 M Ground Theory Heights  Heights Targets eval One algebra Map 0b540b7cbc3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets eval One algebra Map 0b540b7cbc3b construction uses the P2 M Ground Theory Heights  Heights Targets eval One algebra Map 0b540b7cbc3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L71-L73

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

theorem P2M_GroundTheory_Heights__Heights_Targets_evalOne_algebraMap_0b540b7cbc3b (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    evalOne i (algebraMap _ (ConeRing i) f) = dehom i f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«evalOne_algebraMap» := P2M_GroundTheory_Heights__Heights_Targets_evalOne_algebraMap_0b540b7cbc3b
