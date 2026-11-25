-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_pow_combination_d88121157b86
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_pow_combination_d88121157b86
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:08:51.83289+00:00
-- url     : https://prove2.me/theorems/34bbf3f6-dd2d-470b-a0ab-4199a0eab8fa
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist exists pow combination d88121157b86: P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist exists pow combinat
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist exists pow combination d88121157b86 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist exists pow combination d88121157b86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L34-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L34-L50

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_pow_combination_d88121157b86 (A : Subalgebra O Ω) {k : ℕ} (f cc : Fin k → Ω)
    (hf : ∀ l, f l ∈ A) (hcc : ∀ l, cc l ∈ A) (hsum : ∑ l, cc l * f l = 1) (N : ℕ) :
    ∃ g : Fin k → Ω, (∀ l, g l ∈ A) ∧ ∑ l, g l * f l ^ N = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«TwistedDualGensExist».«exists_pow_combination» := P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_pow_combination_d88121157b86
