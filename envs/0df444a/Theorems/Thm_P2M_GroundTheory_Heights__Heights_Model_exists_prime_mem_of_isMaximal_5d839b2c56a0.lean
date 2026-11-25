-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_prime_mem_of_isMaximal_5d839b2c56a0
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_prime_mem_of_isMaximal_5d839b2c56a0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:29.171228+00:00
-- url     : https://prove2.me/theorems/544b65e8-8544-4e9c-a6ef-67118b540b49
-- title:
--   P2 M Ground Theory Heights  Heights Model exists prime mem of is Maximal 5d839b2c56a0: P2 M Ground Theory Heights  Heights Model exists prime mem of is Maximal 5d839b2c56a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists prime mem of is Maximal 5d839b2c56a0 construction uses the P2 M Ground Theory Heights  Heights Model exists prime mem of is Maximal 5d839b2c56a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharZero.lean#L28-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureCharZero.lean#L28-L47

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

theorem P2M_GroundTheory_Heights__Heights_Model_exists_prime_mem_of_isMaximal_5d839b2c56a0 (A : Type*) [CommRing A] [Algebra.FiniteType ℤ A]
    (𝔪 : Ideal A) [𝔪.IsMaximal] : ∃ p : ℕ, p.Prime ∧ (p : A) ∈ 𝔪 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_prime_mem_of_isMaximal» := P2M_GroundTheory_Heights__Heights_Model_exists_prime_mem_of_isMaximal_5d839b2c56a0
