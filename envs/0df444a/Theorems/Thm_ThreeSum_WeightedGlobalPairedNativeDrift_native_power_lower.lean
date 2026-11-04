-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedNativeDrift_native_power_lower
-- name    : ThreeSum.WeightedGlobalPairedNativeDrift.native_power_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:13:52.740838+00:00
-- url     : https://prove2.me/theorems/17586bae-ac27-4291-b1fe-e1b8534c98a2
-- title:
--   Weighted Global Paired Native Drift: native power lower
-- statement:
--   The Weighted Global Paired Native Drift construction uses the native power lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedNativeDrift.lean#L18-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedNativeDrift.lean#L18-L30

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalPairedNativeDrift

theorem ThreeSum.WeightedGlobalPairedNativeDrift.native_power_lower (K M R S p : ℕ) (hS : M≤S^K)
    (hp : M*R*S^2≤p^2) :
    M^(K+2)*R^K≤p^(2*K) := by sorry
