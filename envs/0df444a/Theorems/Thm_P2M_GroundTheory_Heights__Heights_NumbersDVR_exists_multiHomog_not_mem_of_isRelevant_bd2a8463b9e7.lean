-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_not_mem_of_isRelevant_bd2a8463b9e7
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_not_mem_of_isRelevant_bd2a8463b9e7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:33.683787+00:00
-- url     : https://prove2.me/theorems/3be774de-c583-4c7c-8b71-a8c4540d044a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog not mem of is Relevant bd2a8463b9e7: P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog not mem of is Relevant bd2a84
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog not mem of is Relevant bd2a8463b9e7 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog not mem of is Relevant bd2a8463b9e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ExistsMultiHomogNotMemOfIsRelevant.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ExistsMultiHomogNotMemOfIsRelevant.lean#L15-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ExistsMultiHomogNotMemOfIsRelevant
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
universe u
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_not_mem_of_isRelevant_bd2a8463b9e7 {H : Ideal (MRing ι R)} (hH : H.IsPrime)
    (hrel : IsRelevant H) (c : K → ℕ) : ∃ m : MRing ι R, IsMultiHomog m c ∧ m ∉ H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_multiHomog_not_mem_of_isRelevant» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_not_mem_of_isRelevant_bd2a8463b9e7
