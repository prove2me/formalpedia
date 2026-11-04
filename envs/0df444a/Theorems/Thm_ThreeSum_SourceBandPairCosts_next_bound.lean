-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairCosts_next_bound
-- name    : ThreeSum.SourceBandPairCosts.next_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:16:47.511695+00:00
-- url     : https://prove2.me/theorems/816bbe7b-a37c-4f2e-9d45-d6e3344de70f
-- title:
--   Source Band Pair Costs: next bound
-- statement:
--   The Source Band Pair Costs construction uses the next bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairCosts.lean#L18-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairCosts.lean#L18-L26

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairCosts
open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData

theorem ThreeSum.SourceBandPairCosts.next_bound (base NL NR g m : ℕ) (hg : 0 < g) :
    next base NL NR g m ≤ base+4*(NL+NR)+
      (BandPartition.size NL g+BandPartition.size NR g)*(3*m+7)+m+9 := by sorry
