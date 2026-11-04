-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceHostBudget_time_bound
-- name    : ThreeSum.LightTernarySourceHostBudget.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:34.39101+00:00
-- url     : https://prove2.me/theorems/0e391cd3-384d-47f0-8e55-d8ea954b206e
-- title:
--   Light Ternary Source Host Budget: time bound
-- statement:
--   The source host pays for all three product dictionaries, all emitted
--   original-position matches, and every map-separated compact bank cell.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHostBudget.lean#L8-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHostBudget.lean#L8-L39

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelBudget
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_957e2f25efb6cbcf
import Definitions.Def_WeightedCache3SUM_Alias_a98211a6e8223f5f
import Theorems.Thm_ThreeSum_LightRadixRows_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketSetup_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_time_bound
import Theorems.Thm_ThreeSum_LightTernaryGroupedSources_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_time_bound
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_time_bound
import Theorems.Thm_ThreeSum_LightWantedJoin_time_bound
import Theorems.Thm_ThreeSum_LightWantedSetup_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceHostBudget
open LightTernarySourceHost

theorem ThreeSum.LightTernarySourceHostBudget.time_bound (xs ys zs : List ℤ) (hxy : ys.length=xs.length) (hxz : zs.length=xs.length)
    (hm : 1≤xs.length) (p J M NL U L bank groups cap : ℕ) (input : ℕ → ℤ)
    (hcap : ∀ i<NL, LightHistogram.count
      (fun j => WantedResidueKeys.code M 0 (dictionary xs p J j))
      (WantedResidueKeys.code M 0 (input i)) (size xs J)≤cap) :
    time xs ys zs p J M NL U L bank groups input ≤
      4000*(J+1)*(size xs J+xs.length+1)+
      2000*(NL+size xs J+M+NL*cap+1)*(Nat.log 2 (U+1)+Nat.log 2 (M+1)+1)+
      1000*(L+1)*(NL*cap+groups*bank+1)+500 := by sorry
