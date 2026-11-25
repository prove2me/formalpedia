-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_TelescopeMetric_le_first_1c77e4a9049b
-- name    : P2M_GroundTheory_Heights__Heights_LowerBound_TelescopeMetric_le_first_1c77e4a9049b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:27.10281+00:00
-- url     : https://prove2.me/theorems/c905f3f7-90d8-420a-8e68-7c7dd98823bc
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Telescope Metric le first 1c77e4a9049b: P2 M Ground Theory Heights  Heights Lower Bound Telescope Metric le first 1c77e4a9049b
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Telescope Metric le first 1c77e4a9049b construction uses the P2 M Ground Theory Heights  Heights Lower Bound Telescope Metric le first 1c77e4a9049b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PTelescopeMetric.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PTelescopeMetric.lean#L7-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PTelescopeMetric
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

theorem P2M_GroundTheory_Heights__Heights_LowerBound_TelescopeMetric_le_first_1c77e4a9049b {n : ℕ} {I : ℕ → ℝ} (h : ∀ i, i < n → I (i + 1) ≤ I i) :
    ∀ i, i ≤ n → I i ≤ I 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBound».«TelescopeMetric».«le_first» := P2M_GroundTheory_Heights__Heights_LowerBound_TelescopeMetric_le_first_1c77e4a9049b
