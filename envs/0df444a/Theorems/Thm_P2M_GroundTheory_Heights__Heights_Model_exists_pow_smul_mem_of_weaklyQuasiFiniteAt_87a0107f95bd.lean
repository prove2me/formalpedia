-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_of_weaklyQuasiFiniteAt_87a0107f95bd
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_of_weaklyQuasiFiniteAt_87a0107f95bd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:09.960285+00:00
-- url     : https://prove2.me/theorems/8eeac30d-05af-4383-9e87-9a81cf898718
-- title:
--   P2 M Ground Theory Heights  Heights Model exists pow smul mem of weakly Quasi Finite At 87a0107f95bd: P2 M Ground Theory Heights  Heights Model exists pow smul mem of weakly Quasi Finite At 87a0107f95
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists pow smul mem of weakly Quasi Finite At 87a0107f95bd construction uses the P2 M Ground Theory Heights  Heights Model exists pow smul mem of weakly Quasi Finite At 87a0107f95bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureLocal.lean#L36-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureLocal.lean#L36-L163

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureLocal
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

theorem P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_of_weaklyQuasiFiniteAt_87a0107f95bd
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (d : ℕ) [Algebra (MvPolynomial (Fin d) ℤ) A]
    (hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℤ) A))
    [Algebra.FiniteType (MvPolynomial (Fin d) ℤ) A]
    (𝔪 : Ideal A) [𝔪.IsPrime] [Algebra.WeaklyQuasiFiniteAt (MvPolynomial (Fin d) ℤ) 𝔪] :
    ∃ r ∉ 𝔪, ∃ N : Submodule A (integralClosure A K), N.FG ∧
      ∀ x : integralClosure A K, ∃ n : ℕ, r ^ n • x ∈ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_pow_smul_mem_of_weaklyQuasiFiniteAt» := P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_of_weaklyQuasiFiniteAt_87a0107f95bd
