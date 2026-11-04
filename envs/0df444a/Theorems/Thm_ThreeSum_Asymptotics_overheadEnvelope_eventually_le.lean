-- Prove2me | Theorems.Thm_ThreeSum_Asymptotics_overheadEnvelope_eventually_le
-- name    : ThreeSum.Asymptotics.overheadEnvelope_eventually_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:32.523569+00:00
-- url     : https://prove2.me/theorems/143d68a2-d65b-4186-99f3-4b7038d1575f
-- title:
--   Asymptotics: overhead Envelope eventually le
-- statement:
--   Any fixed positive exponent allowance eventually dominates the whole envelope.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Asymptotics.lean#L59-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Asymptotics.lean#L59-L63

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_Asymptotics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Asymptotics
open Filter Real _root_.Asymptotics
open ThreeSum.Parameters
open scoped Topology
set_option maxRecDepth 10000

theorem ThreeSum.Asymptotics.overheadEnvelope_eventually_le {C d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, overheadEnvelope C n ≤ (n : ℝ) ^ d := by sorry
