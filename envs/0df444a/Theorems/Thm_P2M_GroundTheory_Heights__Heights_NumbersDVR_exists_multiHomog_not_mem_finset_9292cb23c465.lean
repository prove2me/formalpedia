-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_not_mem_finset_9292cb23c465
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_not_mem_finset_9292cb23c465
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:11:47.747809+00:00
-- url     : https://prove2.me/theorems/b35ea648-a372-4a9d-bfb2-c0e9e09f37ef
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog not mem finset 9292cb23c465: P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog not mem finset 9292cb23c465
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog not mem finset 9292cb23c465 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog not mem finset 9292cb23c465 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ExistsMultiHomogNotMemOfIsRelevant.lean#L31-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ExistsMultiHomogNotMemOfIsRelevant.lean#L31-L72

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_not_mem_finset_9292cb23c465 [Infinite R] (c : K → ℕ) (S : Finset (Ideal (MRing ι R)))
    (hS : ∀ Q ∈ S, Q.IsPrime ∧ IsRelevant Q ∧ ∀ a : R, C a ∈ Q → a = 0) :
    ∃ m : MRing ι R, IsMultiHomog m c ∧ ∀ Q ∈ S, m ∉ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_multiHomog_not_mem_finset» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_not_mem_finset_9292cb23c465
