-- Prove2me | Theorems.Thm_ThreeSum_BandScales_bandSize_ge_unrounded
-- name    : ThreeSum.BandScales.bandSize_ge_unrounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:40.017206+00:00
-- url     : https://prove2.me/theorems/da962294-1f81-40f2-b0a1-af4b45ad2523
-- title:
--   Band Scales: band Size ge unrounded
-- statement:
--   The Band Scales construction uses the band Size ge unrounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean#L145-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean#L145-L150

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.BandScales.bandSize_ge_unrounded (n : ℕ) : unroundedBand n ≤ (bandSize n : ℝ) := by sorry
