-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_ratio_mem_f4c4da77c024
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_ratio_mem_f4c4da77c024
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:07:10.142802+00:00
-- url     : https://prove2.me/theorems/47b0dc07-0241-4b26-be72-8e46db63b9c9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models ratio mem f4c4da77c024: P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models ratio mem f4c4da77c024
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models ratio mem f4c4da77c024 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models ratio mem f4c4da77c024 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinTwoModels.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinTwoModels.lean#L23-L27

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_ratio_mem_f4c4da77c024 {K' : Type} {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : fnField O (joinCoord x z) = fnField O x) (k : K') (i j : ι' k) :
    z ⟨k, i⟩ / z ⟨k, j⟩ ∈ fnField O x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinTwoModels».«ratio_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_ratio_mem_f4c4da77c024
