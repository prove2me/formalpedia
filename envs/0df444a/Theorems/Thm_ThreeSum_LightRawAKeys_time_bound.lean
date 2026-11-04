-- Prove2me | Theorems.Thm_ThreeSum_LightRawAKeys_time_bound
-- name    : ThreeSum.LightRawAKeys.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:56:33.98619+00:00
-- url     : https://prove2.me/theorems/1205fd51-c802-42b1-a304-6a87235d1a62
-- title:
--   Light Raw AKeys: time bound
-- statement:
--   The Light Raw AKeys construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRawAKeys.lean#L126-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRawAKeys.lean#L126-L128

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_957e2f25efb6cbcf
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightRawAKeys
open Light LightResidues RawIncidences RawAKeyLists
set_option maxHeartbeats 1000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightRawAKeys.time_bound (n U : ℕ) : time n U ≤ 220*(n+1)*(Nat.log 2 (U+1)+1) := by sorry
