-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_evalOne_ratioMap_8be7c5deb8d9
-- name    : P2M_GroundTheory_Heights__Heights_Targets_evalOne_ratioMap_8be7c5deb8d9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:03:03.974018+00:00
-- url     : https://prove2.me/theorems/a0b40461-753b-4fa3-ba47-09f790e17d56
-- title:
--   P2 M Ground Theory Heights  Heights Targets eval One ratio Map 8be7c5deb8d9: P2 M Ground Theory Heights  Heights Targets eval One ratio Map 8be7c5deb8d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets eval One ratio Map 8be7c5deb8d9 construction uses the P2 M Ground Theory Heights  Heights Targets eval One ratio Map 8be7c5deb8d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L102-L103

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

theorem P2M_GroundTheory_Heights__Heights_Targets_evalOne_ratioMap_8be7c5deb8d9 (i : (k : K) → ι k) (g : DehomRing i) : evalOne i (ratioMap i g) = g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«evalOne_ratioMap» := P2M_GroundTheory_Heights__Heights_Targets_evalOne_ratioMap_8be7c5deb8d9
