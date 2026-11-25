-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_lt_max_zero_log_div_iff_c2c029cf849b
-- name    : P2M_GroundTheory_Heights__Heights_LowerBound_lt_max_zero_log_div_iff_c2c029cf849b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:50.19156+00:00
-- url     : https://prove2.me/theorems/32dd9ac8-f554-4a42-9a11-8c7efc81efe6
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound lt max zero log div iff c2c029cf849b: P2 M Ground Theory Heights  Heights Lower Bound lt max zero log div iff c2c029cf849b
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound lt max zero log div iff c2c029cf849b construction uses the P2 M Ground Theory Heights  Heights Lower Bound lt max zero log div iff c2c029cf849b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PMeanLogPlus.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/PMeanLogPlus.lean#L13-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PMeanLogPlus
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
open Real MeasureTheory Filter Topology Set
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_LowerBound_lt_max_zero_log_div_iff_c2c029cf849b {t r l : ℝ} (ht : 0 < t) (hr : 0 < r) (hl : 0 < l) :
    t < max 0 (log (r / l)) ↔ l < exp (-t) * r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBound».«lt_max_zero_log_div_iff» := P2M_GroundTheory_Heights__Heights_LowerBound_lt_max_zero_log_div_iff_c2c029cf849b
