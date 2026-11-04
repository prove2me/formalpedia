-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_native_family_covers
-- name    : ThreeSum.WeightedGlobalOversizePrime.native_family_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:04.097194+00:00
-- url     : https://prove2.me/theorems/0dba990c-81aa-4b47-91f3-19b852124a83
-- title:
--   Weighted Global Oversize Prime: native family covers
-- statement:
--   The Weighted Global Oversize Prime construction uses the native family covers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L167-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L167-L180

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalOversizePrime.native_family_covers {K m k : ℕ} (hK : 0 < K) (hm : 0 < m) (hk : 0 < k)
    (t : ZMod (nativePrime K m) × ZMod (nativePrime K m)) :
    ∃ w ∈ nativeFamily K m k, Covers m (nativePrime K m) (sourceCap m (nativePrime K m))
      (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k) w t := by sorry
