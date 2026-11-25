-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_dehom_surjective_7ef87700430c
-- name    : P2M_GroundTheory_Heights__Heights_Targets_dehom_surjective_7ef87700430c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:02:59.560219+00:00
-- url     : https://prove2.me/theorems/2dcfc364-128b-5f4a-b7b7-e2fd930b8840
-- title:
--   P2 M Ground Theory Heights  Heights Targets dehom surjective 7ef87700430c: P2 M Ground Theory Heights  Heights Targets dehom surjective 7ef87700430c
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets dehom surjective 7ef87700430c construction uses the P2 M Ground Theory Heights  Heights Targets dehom surjective 7ef87700430c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L64-L65

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
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Targets_dehom_surjective_7ef87700430c (i : (k : K) → ι k) : Function.Surjective (dehom i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«dehom_surjective» := P2M_GroundTheory_Heights__Heights_Targets_dehom_surjective_7ef87700430c
