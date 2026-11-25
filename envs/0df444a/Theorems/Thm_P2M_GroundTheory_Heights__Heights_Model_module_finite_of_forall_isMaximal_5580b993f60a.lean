-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_module_finite_of_forall_isMaximal_5580b993f60a
-- name    : P2M_GroundTheory_Heights__Heights_Model_module_finite_of_forall_isMaximal_5580b993f60a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:41.217627+00:00
-- url     : https://prove2.me/theorems/74d8c22a-73e8-5439-9c65-329d52c9eab2
-- title:
--   P2 M Ground Theory Heights  Heights Model module finite of forall is Maximal 5580b993f60a: P2 M Ground Theory Heights  Heights Model module finite of forall is Maximal 5580b993f60a
-- statement:
--   The P2 M Ground Theory Heights  Heights Model module finite of forall is Maximal 5580b993f60a construction uses the P2 M Ground Theory Heights  Heights Model module finite of forall is Maximal 5580b993f60a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureLocal.lean#L8-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/FiniteIntegralClosureLocal.lean#L8-L34

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

theorem P2M_GroundTheory_Heights__Heights_Model_module_finite_of_forall_isMaximal_5580b993f60a {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal →
      ∃ r ∉ 𝔪, ∃ N : Submodule A M, N.FG ∧ ∀ x : M, ∃ n : ℕ, r ^ n • x ∈ N) :
    Module.Finite A M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«module_finite_of_forall_isMaximal» := P2M_GroundTheory_Heights__Heights_Model_module_finite_of_forall_isMaximal_5580b993f60a
