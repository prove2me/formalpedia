-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_ratioMap_fd9f5e3b1f68
-- name    : P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_ratioMap_fd9f5e3b1f68
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:14:14.35231+00:00
-- url     : https://prove2.me/theorems/eb8d23ff-e2ab-5bba-ba61-103143f88d69
-- title:
--   P2 M Ground Theory Heights  Heights Targets eval One comp ratio Map fd9f5e3b1f68: P2 M Ground Theory Heights  Heights Targets eval One comp ratio Map fd9f5e3b1f68
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets eval One comp ratio Map fd9f5e3b1f68 construction uses the P2 M Ground Theory Heights  Heights Targets eval One comp ratio Map fd9f5e3b1f68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L79-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L79-L100

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

theorem P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_ratioMap_fd9f5e3b1f68 (i : (k : K) → ι k) : (evalOne i).comp (ratioMap i) = RingHom.id _ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«evalOne_comp_ratioMap» := P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_ratioMap_fd9f5e3b1f68
