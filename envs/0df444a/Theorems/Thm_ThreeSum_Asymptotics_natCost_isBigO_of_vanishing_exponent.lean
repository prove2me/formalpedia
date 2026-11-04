-- Prove2me | Theorems.Thm_ThreeSum_Asymptotics_natCost_isBigO_of_vanishing_exponent
-- name    : ThreeSum.Asymptotics.natCost_isBigO_of_vanishing_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:34.002316+00:00
-- url     : https://prove2.me/theorems/91e527db-659c-459b-8dcc-41fd516ba427
-- title:
--   Asymptotics: nat Cost is Big O of vanishing exponent
-- statement:
--   Generic absorption. Its cost hypothesis is explicit, and is not supplied by arithmetic.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Asymptotics.lean#L66-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Asymptotics.lean#L66-L78

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

theorem ThreeSum.Asymptotics.natCost_isBigO_of_vanishing_exponent {T : ℕ → ℕ} {w : ℕ → ℝ}
    (hw : Tendsto w atTop (𝓝 0))
    (hcost : ∀ᶠ n : ℕ in atTop,
      (T n : ℝ) ≤ (n : ℝ) ^ (certificateExponent + w n)) :
    (fun n : ℕ => (T n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ targetExponent) := by sorry
