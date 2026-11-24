-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_secIdeal_9ac050eb4a81
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_secIdeal_9ac050eb4a81
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:18.065801+00:00
-- url     : https://prove2.me/theorems/28cc3ecb-96d1-48d2-9759-6f36560912cd
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mem sec Ideal 9ac050eb4a81: P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mem sec Ideal 9ac050eb4a81
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mem sec Ideal 9ac050eb4a81 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Index Linear Alt mem sec Ideal 9ac050eb4a81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L72-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean#L72-L89

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_secIdeal_9ac050eb4a81 {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ} {z : Ω} :
    z ∈ secIdeal y c a ↔ ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) → z / gen y c a c' ∈ chartRingZ y c' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveIndexLinearAlt».«mem_secIdeal» := P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_mem_secIdeal_9ac050eb4a81
