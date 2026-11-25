-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_exists_ne_zero_6aec105870c0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_exists_ne_zero_6aec105870c0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:43.33878+00:00
-- url     : https://prove2.me/theorems/3a9752dc-9626-56f3-b93d-dab97d442cd5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models exists ne zero 6aec105870c0: P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models exists ne zero 6aec105870c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models exists ne zero 6aec105870c0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Two Models exists ne zero 6aec105870c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinTwoModels.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinTwoModels.lean#L52-L59

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
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_exists_ne_zero_6aec105870c0 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    {d : ℕ} (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinTwoModels».«exists_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_exists_ne_zero_6aec105870c0
