-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_patch_read_same
-- name    : ThreeSum.LightWeightedGlobalPrefixHeader.patch_read_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:42:02.853845+00:00
-- url     : https://prove2.me/theorems/dbd5d704-7a50-4b3b-ba41-26f4341f069e
-- title:
--   Light Weighted Global Prefix Header: patch read same
-- statement:
--   The Light Weighted Global Prefix Header construction uses the patch read same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L52-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L52-L58

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixHeader.patch_read_same (base : ℕ) (loc μ : ℕ→ ℤ) (fs : List (ℕ×ℕ)) (i : ℕ)
    (hn : ∀ ir∈fs, ir.1≠i) : patch base loc μ fs (base+i)=μ (base+i) := by sorry
