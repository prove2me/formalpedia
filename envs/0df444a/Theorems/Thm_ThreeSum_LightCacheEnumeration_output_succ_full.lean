-- Prove2me | Theorems.Thm_ThreeSum_LightCacheEnumeration_output_succ_full
-- name    : ThreeSum.LightCacheEnumeration.output_succ_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:47.397829+00:00
-- url     : https://prove2.me/theorems/45800016-3aae-492b-b638-06f1512c6580
-- title:
--   Light Cache Enumeration: output succ full
-- statement:
--   The Light Cache Enumeration construction uses the output succ full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L43-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L43-L47

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_LightEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightCacheEnumeration.output_succ_full {T : ℕ} (hT : 1025 ≤ T) (N pref : ℕ) :
    output (N+1) T pref = output N T pref ++
      output N (T-512) (pref+4^N) ++ output N (T-1025) (pref+3*4^N) := by sorry
