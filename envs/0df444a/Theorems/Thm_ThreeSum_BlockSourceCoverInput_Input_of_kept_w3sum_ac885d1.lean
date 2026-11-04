-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceCoverInput_Input_of_kept_w3sum_ac885d1
-- name    : ThreeSum.BlockSourceCoverInput.Input.of_kept_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:42.215825+00:00
-- url     : https://prove2.me/theorems/21225d18-9830-437b-9711-7d79a757ac88
-- title:
--   Input: of kept
-- statement:
--   The Input construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCoverInput.lean#L45-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCoverInput.lean#L45-L75

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
import Definitions.Def_Submission_ThreeSum_BlockSourceCoverInput
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCoverInput
open Light GlobalEncoding LocalCoverBounds BlockCoefficientRows BlockSourceFlags

theorem ThreeSum.BlockSourceCoverInput.Input.of_kept_w3sum_ac885d1 {μ ν : ℕ → ℤ} {h maps candidates histL histR bound : ℕ}
    (H : Input μ h maps candidates histL histR) (K : Kept μ ν bound)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ bound)
    (hcandidates : candidates+scheduleSize h ≤ bound)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ bound)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ bound) :
    Input ν h maps candidates histL histR := by sorry
