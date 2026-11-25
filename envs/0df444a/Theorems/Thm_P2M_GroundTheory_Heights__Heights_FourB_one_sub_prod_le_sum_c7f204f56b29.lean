-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_one_sub_prod_le_sum_c7f204f56b29
-- name    : P2M_GroundTheory_Heights__Heights_FourB_one_sub_prod_le_sum_c7f204f56b29
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:14.511622+00:00
-- url     : https://prove2.me/theorems/0fbdc9a3-e4ed-5567-9a63-b4117419a88b
-- title:
--   P2 M Ground Theory Heights  Heights Four B one sub prod le sum c7f204f56b29: P2 M Ground Theory Heights  Heights Four B one sub prod le sum c7f204f56b29
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B one sub prod le sum c7f204f56b29 construction uses the P2 M Ground Theory Heights  Heights Four B one sub prod le sum c7f204f56b29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PDegreeRatio.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PDegreeRatio.lean#L7-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PDegreeRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB

theorem P2M_GroundTheory_Heights__Heights_FourB_one_sub_prod_le_sum_c7f204f56b29 {ι : Type*} (s : Finset ι) (g h : ι → ℝ)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1) (hgh : ∀ i, 1 - g i ≤ h i) :
    1 - ∏ i ∈ s, g i ≤ ∑ i ∈ s, h i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«one_sub_prod_le_sum» := P2M_GroundTheory_Heights__Heights_FourB_one_sub_prod_le_sum_c7f204f56b29
