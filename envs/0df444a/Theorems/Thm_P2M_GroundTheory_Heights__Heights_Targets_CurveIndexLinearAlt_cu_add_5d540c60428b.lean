-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_add_5d540c60428b
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_add_5d540c60428b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:49.290831+00:00
-- url     : https://prove2.me/theorems/cf32f8b6-126c-4a6b-b437-1dd3483f1d8c
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu add 5d540c60428b: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu add 5d540c60428b
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu add 5d540c60428b construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu add 5d540c60428b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L31-L34

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_add_5d540c60428b {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a a' : K → ℤ) :
    cu y c (a + a') = cu y c a * cu y c a' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«cu_add» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_add_5d540c60428b
