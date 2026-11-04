-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixHeader_result_segment
-- name    : ThreeSum.LightWeightedGlobalPrefixHeader.result_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:49:06.368099+00:00
-- url     : https://prove2.me/theorems/f1da8181-aea3-4d8e-b8d9-81d65b89b1b0
-- title:
--   Light Weighted Global Prefix Header: result segment
-- statement:
--   Exact segment conversion for the actual finite header writes.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean#L56-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean#L56-L70

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixHeader
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixHeader
open Light
set_option maxHeartbeats 4000000

theorem ThreeSum.LightWeightedGlobalPrefixHeader.result_segment {μ μ₀ ν : ℕ→ℤ} {template live hdr s m p power alpha2 alphaRank localQ radix J
    N T L groups nb bank powers Fbase Gbase : ℕ} {ret : ℤ} {xs : List ℤ}
    (hlen : xs.length=106) (hxs : Seg μ template xs)
    (hcopy : ∀i<106, μ₀ (live+i)=μ (template+i))
    (hν : ν=Function.update (patch live
      (frame (args template live hdr s m p power alpha2 alphaRank localQ radix J++
        locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase++[ret]))
      μ₀ LightWeightedGlobalPrefixLoop.headerWrites) (live+104) 0) :
    Seg ν live (resultHeader xs template live hdr s m p power alpha2 alphaRank localQ radix J
      N T L groups nb bank powers Fbase Gbase ret) := by sorry
