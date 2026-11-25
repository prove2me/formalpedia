-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_mem_integer_of_mem_chartRingZ_c3014f939b0b
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_mem_integer_of_mem_chartRingZ_c3014f939b0b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:55.338988+00:00
-- url     : https://prove2.me/theorems/e66a2754-d3e4-51aa-8317-8bc4ce3613f3
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt mem integer of mem chart Ring Z c3014f939b0b: P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt mem integer of mem cha
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt mem integer of mem chart Ring Z c3014f939b0b construction uses the P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt mem integer of mem chart Ring Z c3014f939b0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveRingFinite.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveRingFinite.lean#L18-L31

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_mem_integer_of_mem_chartRingZ_c3014f939b0b {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (z : (Σ k, ι k) → F) (c : ∀ k, ι k)
    (hc : ∀ p : Σ k, ι k, v.valuation F (z p) ≤ v.valuation F (z ⟨p.1, c p.1⟩)) {b : F}
    (hb : b ∈ chartRingZ z c) : b ∈ (v.valuation F).integer := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveRingFiniteAlt».«mem_integer_of_mem_chartRingZ» := P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_mem_integer_of_mem_chartRingZ_c3014f939b0b
