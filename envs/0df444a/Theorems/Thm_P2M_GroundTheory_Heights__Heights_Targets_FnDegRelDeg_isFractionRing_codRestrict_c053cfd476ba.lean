-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_isFractionRing_codRestrict_c053cfd476ba
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_isFractionRing_codRestrict_c053cfd476ba
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:41:01.821568+00:00
-- url     : https://prove2.me/theorems/66986457-68fa-4c38-955f-b2663409138a
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg is Fraction Ring cod Restrict c053cfd476ba: P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg is Fraction Ring cod Restrict c053cfd4
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg is Fraction Ring cod Restrict c053cfd476ba construction uses the P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg is Fraction Ring cod Restrict c053cfd476ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L27-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg

theorem P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_isFractionRing_codRestrict_c053cfd476ba {R L F' : Type*} [CommRing R] [Field L] [Field F'] [Algebra F' L]
    (E : IntermediateField F' L) (τ : R →+* L) (hτ : Function.Injective τ) (hmem : ∀ x, τ x ∈ E)
    (hq : ∀ z ∈ E, ∃ x y, z = τ x / τ y) :
    letI := (τ.codRestrict E hmem).toAlgebra
    IsFractionRing R E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FnDegRelDeg».«isFractionRing_codRestrict» := P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_isFractionRing_codRestrict_c053cfd476ba
