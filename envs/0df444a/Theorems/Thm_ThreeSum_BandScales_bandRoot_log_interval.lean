-- Prove2me | Theorems.Thm_ThreeSum_BandScales_bandRoot_log_interval
-- name    : ThreeSum.BandScales.bandRoot_log_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:27.021952+00:00
-- url     : https://prove2.me/theorems/f7c6a98c-29f5-47ad-9f86-714ecb67550a
-- title:
--   Band Scales: band Root log interval
-- statement:
--   The Band Scales construction uses the band Root log interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean#L60-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean#L60-L73

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.BandScales.bandRoot_log_interval (n : ℕ) :
    Real.log (typedOutputs n : ℝ) ≤ 2 * Real.log (bandRoot n : ℝ) ∧
      2 * Real.log (bandRoot n : ℝ) ≤ Real.log 4 + Real.log (typedOutputs n : ℝ) := by sorry
