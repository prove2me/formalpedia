-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mul_mem_secIdeal_3d741e7bcfab
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mul_mem_secIdeal_3d741e7bcfab
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:00.728499+00:00
-- url     : https://prove2.me/theorems/d78e5a3c-2406-45cb-9ee7-46808d3cad39
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mul mem sec Ideal 3d741e7bcfab: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mul mem sec Ideal 3d741e7bcfab
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mul mem sec Ideal 3d741e7bcfab construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mul mem sec Ideal 3d741e7bcfab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L93-L99

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mul_mem_secIdeal_3d741e7bcfab {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ} :
    ∀ b ∈ curveRing y, ∀ z ∈ secIdeal y c a, b * z ∈ secIdeal y c a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«mul_mem_secIdeal» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mul_mem_secIdeal_3d741e7bcfab
