-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_mem_integralClosure_b8f04dd67a29
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_mem_integralClosure_b8f04dd67a29
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:09.113813+00:00
-- url     : https://prove2.me/theorems/3990a4d0-94d9-4a48-8a11-d02d4792c490
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt mem integral Closure b8f04dd67a29: P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt mem integral Closure b8f04dd67a29
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt mem integral Closure b8f04dd67a29 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt mem integral Closure b8f04dd67a29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveRingFinite.lean#L35-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveRingFinite.lean#L35-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveRingFinite
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveRingFiniteAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_mem_integralClosure_b8f04dd67a29 {F : Type} [Field F] [NumberField F] (z : (Σ k, ι k) → F) (c0 : ∀ k, ι k)
    (hc0 : ∀ k, z ⟨k, c0 k⟩ ≠ 0) {b : F}
    (hb : ∀ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) → b ∈ chartRingZ z c) :
    b ∈ integralClosure ℤ F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveRingFiniteAlt».«mem_integralClosure» := P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_mem_integralClosure_b8f04dd67a29
