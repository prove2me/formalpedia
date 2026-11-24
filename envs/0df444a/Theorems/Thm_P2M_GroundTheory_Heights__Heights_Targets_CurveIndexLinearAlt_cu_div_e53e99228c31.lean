-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_div_e53e99228c31
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_div_e53e99228c31
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:35:27.71523+00:00
-- url     : https://prove2.me/theorems/dc144b2f-3e0f-4b4e-9fab-612b9562cd79
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu div e53e99228c31: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu div e53e99228c31
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu div e53e99228c31 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt cu div e53e99228c31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L38-L41

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_div_e53e99228c31 (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) (a : K → ℤ) :
    cu y c' a / cu y c a = ∏ k, (y ⟨k, c' k⟩ / y ⟨k, c k⟩) ^ a k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«cu_div» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_div_e53e99228c31
