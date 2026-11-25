-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_zpow_mem_of_9a48d073fbd3
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_zpow_mem_of_9a48d073fbd3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:57.0045+00:00
-- url     : https://prove2.me/theorems/28d9d806-1693-4c25-9f5d-22af28b5dd1f
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt zpow mem of 9a48d073fbd3: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt zpow mem of 9a48d073fbd3
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt zpow mem of 9a48d073fbd3 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt zpow mem of 9a48d073fbd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L143-L146

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_zpow_mem_of_9a48d073fbd3 {S : Subring Ω} {x : Ω} (hx : x ∈ S) (hx' : x⁻¹ ∈ S) (n : ℤ) : x ^ n ∈ S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«zpow_mem_of» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_zpow_mem_of_9a48d073fbd3
