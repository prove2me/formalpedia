-- Prove2me | Theorems.Thm_ThreeSum_TrimScales_localPrime_sq_le_power_w3sum_ac885d1
-- name    : ThreeSum.TrimScales.localPrime_sq_le_power_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:05.970624+00:00
-- url     : https://prove2.me/theorems/643982a9-84dc-4554-b124-130886dbebc2
-- title:
--   Trim Scales: local Prime sq le power
-- statement:
--   The Trim Scales construction uses the local Prime sq le power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L168-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L168-L180

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.TrimScales.localPrime_sq_le_power_w3sum_ac885d1 (h : ℕ) :
    LocalCoverBounds.localPrime h ^ 2 ≤ 2 ^ (4 + 514 * h) := by sorry
