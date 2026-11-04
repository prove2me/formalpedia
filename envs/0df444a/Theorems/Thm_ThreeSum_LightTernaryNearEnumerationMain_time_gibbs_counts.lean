-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_time_gibbs_counts
-- name    : ThreeSum.LightTernaryNearEnumerationMain.time_gibbs_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:57.058113+00:00
-- url     : https://prove2.me/theorems/89eac81c-57c4-41d9-8aa9-2cfe535ab388
-- title:
--   Light Ternary Near Enumeration Main: time gibbs counts
-- statement:
--   The actual recursive machine time is paid by the same finite Gibbs query bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumerationMain.lean#L242-L262
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumerationMain.lean#L242-L262

import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration ThreeSum.LightTernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearEnumerationMain.time_gibbs_counts {N : ℕ} (Q : ThreeSum.TernaryJointType.TritWord N)
    (D : ℕ) (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (time (ThreeSum.TernaryBankEnumeration.wordList Q) D : ℝ)*z^D ≤
      900*(N+1)*(1+z)^ThreeSum.TernaryJointType.digitCount Q 1 *
        (1+z+z^2)^ThreeSum.TernaryJointType.digitCount Q 2 := by sorry
