-- Prove2me | Theorems.Thm_ThreeSum_BandScales_mu_div_twenty_real
-- name    : ThreeSum.BandScales.mu_div_twenty_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:25.892988+00:00
-- url     : https://prove2.me/theorems/474cafd3-9385-4f16-97ff-0acbd4023fb1
-- title:
--   Band Scales: mu div twenty real
-- statement:
--   The Band Scales construction uses the mu div twenty real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean#L104-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandScales.lean#L104-L107

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.BandScales.mu_div_twenty_real (n : ℕ) : (mu n / 20 : ℕ) = (mu n : ℝ) / 20 := by sorry
