-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_module_finite_of_semilinear_0775f0fbfa71
-- name    : P2M_GroundTheory_Heights__Heights_Model_module_finite_of_semilinear_0775f0fbfa71
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:56.153682+00:00
-- url     : https://prove2.me/theorems/f97f3c33-5244-4ce6-8048-361c6576a25f
-- title:
--   P2 M Ground Theory Heights  Heights Model module finite of semilinear 0775f0fbfa71: P2 M Ground Theory Heights  Heights Model module finite of semilinear 0775f0fbfa71
-- statement:
--   The P2 M Ground Theory Heights  Heights Model module finite of semilinear 0775f0fbfa71 construction uses the P2 M Ground Theory Heights  Heights Model module finite of semilinear 0775f0fbfa71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharP.lean#L8-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharP.lean#L8-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model

theorem P2M_GroundTheory_Heights__Heights_Model_module_finite_of_semilinear_0775f0fbfa71 {B R M N : Type*} [CommRing B] [CommRing R] [Algebra R B]
    [IsNoetherianRing R] [Module.Finite R B] [AddCommGroup M] [Module B M] [AddCommGroup N]
    [Module B N] [Module R N] [IsScalarTower R B N] [Module.Finite B N]
    (σ : B →+* R) (hσ : Function.Surjective σ) (φ : M →+ N) (hφ : Function.Injective φ)
    (hφσ : ∀ (b : B) (m : M), φ (b • m) = σ b • φ m) : Module.Finite B M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«module_finite_of_semilinear» := P2M_GroundTheory_Heights__Heights_Model_module_finite_of_semilinear_0775f0fbfa71
