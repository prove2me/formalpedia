-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_of_isMaximal_e0c1554fd021
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_of_isMaximal_e0c1554fd021
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:17.39484+00:00
-- url     : https://prove2.me/theorems/69d6944f-900a-487c-a00c-e516e25bdbd1
-- title:
--   P2 M Ground Theory Heights  Heights Model exists pow smul mem of is Maximal e0c1554fd021: P2 M Ground Theory Heights  Heights Model exists pow smul mem of is Maximal e0c1554fd021
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists pow smul mem of is Maximal e0c1554fd021 construction uses the P2 M Ground Theory Heights  Heights Model exists pow smul mem of is Maximal e0c1554fd021 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharZero.lean#L49-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharZero.lean#L49-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
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

theorem P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_of_isMaximal_e0c1554fd021
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ∃ r ∉ 𝔪, ∃ N : Submodule A (integralClosure A K), N.FG ∧
      ∀ x : integralClosure A K, ∃ n : ℕ, r ^ n • x ∈ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_pow_smul_mem_of_isMaximal» := P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_of_isMaximal_e0c1554fd021
