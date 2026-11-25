-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipMap_mem_c41bae6a48c7
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipMap_mem_c41bae6a48c7
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:55:17.739627+00:00
-- url     : https://prove2.me/theorems/91513d71-401d-4fda-a9e3-3aed25a1fb34
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Map mem c41bae6a48c7: P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Map mem c41bae6a48c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Map mem c41bae6a48c7 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Rational Unipotent unip Map mem c41bae6a48c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean#L86-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRationalUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipMap_mem_c41bae6a48c7 (h : HermitianForm F E W) {La : AddSubgroup W}
    (hsm : ∀ (a : 𝓞 E) (x : W), x ∈ La → (a : E) • x ∈ La) (hint : IsIntegralOn h La)
    {x₀ y : W} {c : E} (hx₀ : x₀ ∈ La) (hy : y ∈ La) (hc : c ∈ integralClosure ℤ E)
    {x : W} (hx : x ∈ La) : unipMap h x₀ y c x ∈ La := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«RationalUnipotent».«unipMap_mem» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipMap_mem_c41bae6a48c7
