-- Prove2me | Theorems.Thm_ThreeSum_BandScales_bandSize_mul_bounds
-- name    : ThreeSum.BandScales.bandSize_mul_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:06:34.253949+00:00
-- url     : https://prove2.me/theorems/d39b750b-4b03-4d31-85d5-f2029cef0ec6
-- title:
--   Band Scales: band Size mul bounds
-- statement:
--   The Band Scales construction uses the band Size mul bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean#L36-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean#L36-L46

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology

theorem ThreeSum.BandScales.bandSize_mul_bounds (n : ℕ) :
    bandRoot n ≤ bandDivisor n * bandSize n ∧
      bandDivisor n * bandSize n < bandRoot n + bandDivisor n := by sorry
