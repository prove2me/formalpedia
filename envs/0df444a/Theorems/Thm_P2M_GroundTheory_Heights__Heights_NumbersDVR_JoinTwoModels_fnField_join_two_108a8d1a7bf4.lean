-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_fnField_join_two_108a8d1a7bf4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_fnField_join_two_108a8d1a7bf4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:18:01.02177+00:00
-- url     : https://prove2.me/theorems/4767bc93-ea2b-45f4-a0b0-a4675d585964
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models fn Field join two 108a8d1a7bf4: P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models fn Field join two 108a8d1a7bf4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models fn Field join two 108a8d1a7bf4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models fn Field join two 108a8d1a7bf4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinTwoModels.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinTwoModels.lean#L29-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinTwoModels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal joinCoord fnField)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels
variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_fnField_join_two_108a8d1a7bf4 {K₁ : Type} {ι₁ : K₁ → Type} {K₂ : Type} {ι₂ : K₂ → Type} (x : (Σ k, ι k) → Ω)
    (z₁ : (Σ k, ι₁ k) → Ω) (z₂ : (Σ k, ι₂ k) → Ω) (h₁ : fnField O (joinCoord x z₁) = fnField O x)
    (h₂ : fnField O (joinCoord x z₂) = fnField O x) :
    fnField O (joinCoord x (joinCoord z₁ z₂)) = fnField O x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinTwoModels».«fnField_join_two» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_fnField_join_two_108a8d1a7bf4
