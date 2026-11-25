-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_X_ffc52befaca7
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_X_ffc52befaca7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:50.963784+00:00
-- url     : https://prove2.me/theorems/0a39091b-1f33-45d8-961f-cdf51e2690c5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field cone Map X ffc52befaca7: P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field cone Map X ffc52befaca7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field cone Map X ffc52befaca7 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field cone Map X ffc52befaca7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PConeTrdegFnField.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PConeTrdegFnField.lean#L52-L54

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_X_ffc52befaca7 (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) :
    ConeTrdegFnField.coneMap (O := O) y c (X k) = C (y ⟨k, c k⟩) * X k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ConeTrdegFnField».«coneMap_X» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_X_ffc52befaca7
