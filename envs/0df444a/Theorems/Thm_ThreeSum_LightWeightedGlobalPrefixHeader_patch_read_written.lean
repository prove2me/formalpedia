-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_patch_read_written
-- name    : ThreeSum.LightWeightedGlobalPrefixHeader.patch_read_written
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:42:11.780838+00:00
-- url     : https://prove2.me/theorems/a166253f-b619-4eed-a85c-9fd3fe8c5cca
-- title:
--   Light Weighted Global Prefix Header: patch read written
-- statement:
--   The Light Weighted Global Prefix Header construction uses the patch read written property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L60-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixHeader.lean#L60-L73

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixHeader.patch_read_written (base : ℕ) (loc μ : ℕ→ ℤ) (fs : List (ℕ×ℕ))
    (hn : (fs.map Prod.fst).Nodup) (ir : ℕ×ℕ) (hir : ir∈fs) :
    patch base loc μ fs (base+ir.1)=loc ir.2 := by sorry
