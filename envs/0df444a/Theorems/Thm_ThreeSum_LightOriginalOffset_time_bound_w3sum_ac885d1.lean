-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalOffset_time_bound_w3sum_ac885d1
-- name    : ThreeSum.LightOriginalOffset.time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:35.169207+00:00
-- url     : https://prove2.me/theorems/c0ab2d6c-e339-49e2-b500-d346470adf88
-- title:
--   Light Original Offset: time bound
-- statement:
--   The Light Original Offset construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean#L209-L224
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean#L209-L224

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightOriginalOffset.time_bound_w3sum_ac885d1 (p nLeft nRight U : ℕ) :
    time p nLeft nRight U ≤ LightKaratsuba.time (Nat.clog 2 p)+252*capacity p+
      131*(nLeft+nRight)*(Nat.log 2 (U+1)+1)+12*Nat.clog 2 p+642 := by sorry
