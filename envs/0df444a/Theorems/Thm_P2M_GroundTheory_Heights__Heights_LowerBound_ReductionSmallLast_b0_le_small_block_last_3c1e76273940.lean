-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_ReductionSmallLast_b0_le_small_block_last_3c1e76273940
-- name    : P2M_GroundTheory_Heights__Heights_LowerBound_ReductionSmallLast_b0_le_small_block_last_3c1e76273940
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:26.960944+00:00
-- url     : https://prove2.me/theorems/630c8323-5658-413e-9a9c-834ba78e1aff
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Reduction Small Last b0 le small block last 3c1e76273940: P2 M Ground Theory Heights  Heights Lower Bound Reduction Small Last b0 le small block last 3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Reduction Small Last b0 le small block last 3c1e76273940 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Reduction Small Last b0 le small block last 3c1e76273940 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PReductionSmallLast.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PReductionSmallLast.lean#L9-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PReductionSmallLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real

theorem P2M_GroundTheory_Heights__Heights_LowerBound_ReductionSmallLast_b0_le_small_block_last_3c1e76273940 {K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La : ℝ}
    (h : ReductionSmallLast.Hyp K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La) :
    b0 ≤ (1 / 2 + Ca + Cc) * La := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBound».«ReductionSmallLast».«b0_le_small_block_last» := P2M_GroundTheory_Heights__Heights_LowerBound_ReductionSmallLast_b0_le_small_block_last_3c1e76273940
