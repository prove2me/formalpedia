-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntermediateRingQuotLength_length_quot_smul_le_04805538deda
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntermediateRingQuotLength_length_quot_smul_le_04805538deda
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:32.417865+00:00
-- url     : https://prove2.me/theorems/b1dcde3a-daa0-4348-9817-757e7cc0a260
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Intermediate Ring Quot Length length quot smul le 04805538deda: P2 M Ground Theory Heights  Heights Numbers DVR Intermediate Ring Quot Length length quo
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Intermediate Ring Quot Length length quot smul le 04805538deda construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Intermediate Ring Quot Length length quot smul le 04805538deda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntermediateRingQuotLength.lean#L19-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntermediateRingQuotLength.lean#L19-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntermediateRingQuotLength
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
universe u
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntermediateRingQuotLength_length_quot_smul_le_04805538deda {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] {M : Type*} [AddCommGroup M] [Module A M] (φ : A →ₗ[A] M)
    (hφ : Function.Injective φ) (htor : ∀ x : M, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range φ)
    {a : A} (ha : a ≠ 0) (hreg : Function.Injective fun x : M => a • x) :
    Module.length A (M ⧸ (a • ⊤ : Submodule A M)) ≤ Module.length A (A ⧸ Ideal.span {a}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntermediateRingQuotLength».«length_quot_smul_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntermediateRingQuotLength_length_quot_smul_le_04805538deda
