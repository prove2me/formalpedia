-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_finsum_eq_finsum_mem_of_support_subset__9f928b0e8d38
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_finsum_eq_finsum_mem_of_support_subset__9f928b0e8d38
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:13.089479+00:00
-- url     : https://prove2.me/theorems/4af4fda9-4ce4-4100-bcf6-83aa1796bfc5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR finsum eq finsum mem of support subset  9f928b0e8d38: P2 M Ground Theory Heights  Heights Numbers DVR finsum eq finsum mem of support subset  9f928b0e8d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR finsum eq finsum mem of support subset  9f928b0e8d38 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR finsum eq finsum mem of support subset  9f928b0e8d38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalCorresp.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalCorresp.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalCorresp
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_finsum_eq_finsum_mem_of_support_subset__9f928b0e8d38 {α : Type*} (f : α → ℤ) {s : Set α}
    (h : Function.support f ⊆ s) : ∑ᶠ i, f i = ∑ᶠ i ∈ s, f i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«finsum_eq_finsum_mem_of_support_subset'» := P2M_GroundTheory_Heights__Heights_NumbersDVR_finsum_eq_finsum_mem_of_support_subset__9f928b0e8d38
