-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_chartLat_one_d525f1fe8df3
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_chartLat_one_d525f1fe8df3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:36.950819+00:00
-- url     : https://prove2.me/theorems/ce894e6f-3dd5-5039-acd9-6a1bcd90f456
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mem chart Lat one d525f1fe8df3: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mem chart Lat one d525f1fe8df3
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mem chart Lat one d525f1fe8df3 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mem chart Lat one d525f1fe8df3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L45-L52

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_chartLat_one_d525f1fe8df3 {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} :
    s ∈ chartLat y a 1 ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → s / cu y c a ∈ chartRingZ y c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«mem_chartLat_one» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_chartLat_one_d525f1fe8df3
