-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedNativeDrift_paired_native_drift
-- name    : ThreeSum.WeightedGlobalPairedNativeDrift.paired_native_drift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:09:10.709763+00:00
-- url     : https://prove2.me/theorems/32f19857-e69c-488a-83b0-6257154723b9
-- title:
--   Weighted Global Paired Native Drift: paired native drift
-- statement:
--   The Weighted Global Paired Native Drift construction uses the paired native drift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedNativeDrift.lean#L32-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedNativeDrift.lean#L32-L57

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalPairedNativeDrift

theorem ThreeSum.WeightedGlobalPairedNativeDrift.paired_native_drift (K M R S p F : ℕ)
    (hS : M≤S^K) (hp : M*R*S^2≤p^2) (hF : (9*F)^4≤M) :
    (9*F*M*R^K)^4*M^(4*K+3)≤(p^(2*K))^4 := by sorry
