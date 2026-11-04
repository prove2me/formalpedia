-- Prove2me | Theorems.Thm_ThreeSum_Switch_switchIndex_le
-- name    : ThreeSum.Switch.switchIndex_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:06:30.274431+00:00
-- url     : https://prove2.me/theorems/9735ca7f-f261-47ce-9d3e-8ea1c5aac37c
-- title:
--   Switch: switch Index le
-- statement:
--   The Switch construction uses the switch Index le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L50-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L50-L54

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0

theorem ThreeSum.Switch.switchIndex_le {J j r q : ℕ} (hq : q ∈ candidates J j r) :
    switchIndex J j r ≤ q := by sorry
