-- Prove2me | Theorems.Thm_ThreeSum_LightBalancedWanted_total_le_div
-- name    : ThreeSum.LightBalancedWanted.total_le_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:38.893148+00:00
-- url     : https://prove2.me/theorems/2c2cf36d-037e-4fdc-8b6a-d55d32d5d13f
-- title:
--   Light Balanced Wanted: total le div
-- statement:
--   The Light Balanced Wanted construction uses the total le div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedWanted.lean#L103-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedWanted.lean#L103-L106

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedWanted
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits}

theorem ThreeSum.LightBalancedWanted.total_le_div (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    total M left right NL NR (LightOriginalOffset.selected M left right NL NR) ≤ NL*NR/M := by sorry
