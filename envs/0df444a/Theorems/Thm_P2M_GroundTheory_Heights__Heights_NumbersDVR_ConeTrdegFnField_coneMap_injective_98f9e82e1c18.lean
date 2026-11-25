-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_injective_98f9e82e1c18
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_injective_98f9e82e1c18
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:52.416666+00:00
-- url     : https://prove2.me/theorems/e04dc411-0016-49fd-bb5c-888b1bfc858a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field cone Map injective 98f9e82e1c18: P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field cone Map injective 98f9e82e1c18
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field cone Map injective 98f9e82e1c18 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field cone Map injective 98f9e82e1c18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PConeTrdegFnField.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PConeTrdegFnField.lean#L60-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConeTrdegFnField
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)
noncomputable section
variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_injective_98f9e82e1c18 (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Function.Injective (ConeTrdegFnField.coneMap (O := O) y c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ConeTrdegFnField».«coneMap_injective» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_injective_98f9e82e1c18
