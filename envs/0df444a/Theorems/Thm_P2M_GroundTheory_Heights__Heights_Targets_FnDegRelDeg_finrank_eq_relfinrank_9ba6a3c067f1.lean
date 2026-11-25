-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_finrank_eq_relfinrank_9ba6a3c067f1
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_finrank_eq_relfinrank_9ba6a3c067f1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:35.513348+00:00
-- url     : https://prove2.me/theorems/256dab5e-23fc-4a56-8120-10f096f17840
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg finrank eq relfinrank 9ba6a3c067f1: P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg finrank eq relfinrank 9ba6a3c067f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg finrank eq relfinrank 9ba6a3c067f1 construction uses the P2 M Ground Theory Heights  Heights Targets Fn Deg Rel Deg finrank eq relfinrank 9ba6a3c067f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L41-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PFnDegRelDeg.lean#L41-L60

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

theorem P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_finrank_eq_relfinrank_9ba6a3c067f1 {F R₁ R₂ L : Type*} [Field F] [CommRing R₁] [CommRing R₂] [Field L]
    [Algebra F L] [Algebra R₁ R₂] (ρ : R₂ →+* L) (hρ : Function.Injective ρ)
    (E H : IntermediateField F L) (hEH : E ≤ H)
    (hτ : Function.Injective (ρ.comp (algebraMap R₁ R₂)))
    (hτE : ∀ x, ρ (algebraMap R₁ R₂ x) ∈ E) (hρH : ∀ x, ρ x ∈ H)
    (hEq : ∀ z ∈ E, ∃ x y, z = ρ (algebraMap R₁ R₂ x) / ρ (algebraMap R₁ R₂ y))
    (hHq : ∀ z ∈ H, ∃ x y, z = ρ x / ρ y) :
    Module.finrank R₁ R₂ = IntermediateField.relfinrank E H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FnDegRelDeg».«finrank_eq_relfinrank» := P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_finrank_eq_relfinrank_9ba6a3c067f1
