-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_patch_outside
-- name    : ThreeSum.LightWeightedGlobalPrefixHeader.patch_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:41:53.136076+00:00
-- url     : https://prove2.me/theorems/f6900489-3018-4853-b432-01dd79fbb233
-- title:
--   Light Weighted Global Prefix Header: patch outside
-- statement:
--   The Light Weighted Global Prefix Header construction uses the patch outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L42-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L42-L50

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixHeader.patch_outside (base : ℕ) (loc μ : ℕ→ ℤ) (fs : List (ℕ×ℕ))
    (hgood : ∀ ir∈fs, ir.1<106) : SameOutside μ (patch base loc μ fs) base 106 := by sorry
