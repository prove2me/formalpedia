-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensSpan_sum_mul_mem_localized_eeeb4b33e5e4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensSpan_sum_mul_mem_localized_eeeb4b33e5e4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:11:47.18526+00:00
-- url     : https://prove2.me/theorems/8a86910e-3b64-43b3-a6e4-c6562971d94a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Span sum mul mem localized eeeb4b33e5e4: P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Span sum mul mem localized
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Span sum mul mem localized eeeb4b33e5e4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Span sum mul mem localized eeeb4b33e5e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensSpan.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensSpan.lean#L11-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensSpan
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensSpan_sum_mul_mem_localized_eeeb4b33e5e4 {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {f : Ω} (hf : f ∈ A) {r : ℕ} (a t : Fin r → Ω)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ A) (ht : ∀ q, t q ∈ A) :
    ∃ n : ℕ, f ^ n * ∑ q, a q * t q ∈ A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«TwistedDualGensSpan».«sum_mul_mem_localized» := P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensSpan_sum_mul_mem_localized_eeeb4b33e5e4
