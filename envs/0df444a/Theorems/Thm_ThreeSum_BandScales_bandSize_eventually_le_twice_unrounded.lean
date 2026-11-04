-- Prove2me | Theorems.Thm_ThreeSum_BandScales_bandSize_eventually_le_twice_unrounded
-- name    : ThreeSum.BandScales.bandSize_eventually_le_twice_unrounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:38:12.549998+00:00
-- url     : https://prove2.me/theorems/ecdb310c-0cdf-4521-b3ba-10baddcf4a08
-- title:
--   Band Scales: band Size eventually le twice unrounded
-- statement:
--   The Band Scales construction uses the band Size eventually le twice unrounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean#L152-L165
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean#L152-L165

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.BandScales.bandSize_eventually_le_twice_unrounded :
    ∀ᶠ n : ℕ in atTop, (bandSize n : ℝ) ≤ 2 * unroundedBand n := by sorry
