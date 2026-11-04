-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSeedCoefficientBudget_wanted_quadratic
-- name    : ThreeSum.WeightedGlobalSeedCoefficientBudget.wanted_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:11:22.981898+00:00
-- url     : https://prove2.me/theorems/7adc2acf-d71c-427b-afb3-d5d0bb468a30
-- title:
--   Weighted Global Seed Coefficient Budget: wanted quadratic
-- statement:
--   Only the logarithm of the full signed-target envelope enters each
--   wanted DFS node, so all prefix overhead remains quadratic in J.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L27-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L27-L41

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSeedCoefficientBudget
open WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalSeedCoefficientBudget.wanted_quadratic (p A J j : ℕ) (hj : j≤J) :
    (LightTernaryWantedCanonical.overhead p (A*(p+1)^j)+
      LightTernaryWantedCanonical.stepCost (A*(p+1)^j)+40)*(j+1)≤
      (1000*(A+2*p+4))*(J+1)^2 := by sorry
