-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_dual_gens_8da4bdc2b4a2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_dual_gens_8da4bdc2b4a2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:09:59.29737+00:00
-- url     : https://prove2.me/theorems/0b8bb947-c321-4394-96cf-dc034ffbd216
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist exists dual gens 8da4bdc2b4a2: P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist exists dual gens 8da4bdc2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist exists dual gens 8da4bdc2b4a2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Twisted Dual Gens Exist exists dual gens 8da4bdc2b4a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L148-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwistedDualGensExist.lean#L148-L161

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_dual_gens_8da4bdc2b4a2 [IsNoetherianRing O] [Fintype τ] {x : τ → Ω}
    (B : ChartBundle O x r E) {c : τ} (hc : x c ≠ 0) :
    ∃ S : Finset (Module.Dual Ω E), (∀ ψ ∈ S, ∀ v ∈ B.lat c, ψ v ∈ chartRing O x c) ∧
      ∀ ψ' : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ' v ∈ chartRing O x c) →
        ∃ u : Module.Dual Ω E → Ω, (∀ ψ, u ψ ∈ chartRing O x c) ∧ ∑ ψ ∈ S, u ψ • ψ = ψ' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«TwistedDualGensExist».«exists_dual_gens» := P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_dual_gens_8da4bdc2b4a2
