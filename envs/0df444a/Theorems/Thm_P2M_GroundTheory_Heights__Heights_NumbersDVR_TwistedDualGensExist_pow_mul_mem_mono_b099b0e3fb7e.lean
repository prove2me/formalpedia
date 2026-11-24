-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_pow_mul_mem_mono_b099b0e3fb7e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_pow_mul_mem_mono_b099b0e3fb7e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:46.025889+00:00
-- url     : https://prove2.me/theorems/3f3f104a-9aec-4295-a617-a99b67b3cf7d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist pow mul mem mono b099b0e3fb7e: P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist pow mul mem mono b099b0e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist pow mul mem mono b099b0e3fb7e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist pow mul mem mono b099b0e3fb7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L100-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist
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
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*}
  {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_pow_mul_mem_mono_b099b0e3fb7e {x : τ → Ω} {c c' : τ} {z : Ω} {n n' : ℕ}
    (h : (x c / x c') ^ n * z ∈ chartRing O x c') (hn : n ≤ n') :
    (x c / x c') ^ n' * z ∈ chartRing O x c' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«TwistedDualGensExist».«pow_mul_mem_mono» := P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_pow_mul_mem_mono_b099b0e3fb7e
