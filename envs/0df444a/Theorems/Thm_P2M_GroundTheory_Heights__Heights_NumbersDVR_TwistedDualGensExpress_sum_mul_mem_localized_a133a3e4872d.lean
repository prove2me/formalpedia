-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExpress_sum_mul_mem_localized_a133a3e4872d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExpress_sum_mul_mem_localized_a133a3e4872d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:10:55.010309+00:00
-- url     : https://prove2.me/theorems/4ce18f04-9f34-4d7c-88ac-695780d10ea4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Express sum mul mem localized a133a3e4872d: P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Express sum mul mem loca
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Express sum mul mem localized a133a3e4872d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Express sum mul mem localized a133a3e4872d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExpress.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExpress.lean#L11-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExpress
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExpress_sum_mul_mem_localized_a133a3e4872d {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {f : Ω} (hf : f ∈ A) {r : ℕ} (a t : Fin r → Ω)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ A) (ht : ∀ q, ∃ n : ℕ, f ^ n * t q ∈ A) :
    ∃ n : ℕ, f ^ n * ∑ q, a q * t q ∈ A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«TwistedDualGensExpress».«sum_mul_mem_localized» := P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExpress_sum_mul_mem_localized_a133a3e4872d
