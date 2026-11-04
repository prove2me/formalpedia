-- Prove2me | Theorems.Thm_ThreeSum_Asymptotics_natCost_isBigO_of_explicit_envelope
-- name    : ThreeSum.Asymptotics.natCost_isBigO_of_explicit_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:34.181709+00:00
-- url     : https://prove2.me/theorems/ff6059e7-6e88-4fc0-9951-491e5fb90e0b
-- title:
--   Asymptotics: nat Cost is Big O of explicit envelope
-- statement:
--   The same bridge with the explicit, separately proved overhead scale.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Asymptotics.lean#L81-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Asymptotics.lean#L81-L88

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

theorem ThreeSum.Asymptotics.natCost_isBigO_of_explicit_envelope {T : ℕ → ℕ} {C : ℝ}
    (hcost : ∀ᶠ n : ℕ in atTop,
      (T n : ℝ) ≤ (n : ℝ) ^ certificateExponent * overheadEnvelope C n) :
    (fun n : ℕ => (T n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ targetExponent) := by sorry
