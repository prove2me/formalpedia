-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairData_ordered
-- name    : ThreeSum.SourceBandPairData.ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:59:29.193821+00:00
-- url     : https://prove2.me/theorems/33c2a9b8-44bd-452c-afe5-2e84bb216d4c
-- title:
--   Source Band Pair Data: ordered
-- statement:
--   The Source Band Pair Data construction uses the ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean#L18-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean#L18-L22

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairData
open Light BandPartition

theorem ThreeSum.SourceBandPairData.ordered (base NL NR g m : ℕ) :
    leftBase base ≤ rightBase base NL g m ∧
    rightBase base NL g m ≤ zeroBase base NL NR g m ∧
    zeroBase base NL NR g m < next base NL NR g m := by sorry
