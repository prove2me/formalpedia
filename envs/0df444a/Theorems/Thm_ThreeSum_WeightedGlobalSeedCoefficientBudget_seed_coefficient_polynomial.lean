-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSeedCoefficientBudget_seed_coefficient_polynomial
-- name    : ThreeSum.WeightedGlobalSeedCoefficientBudget.seed_coefficient_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:14:46.929421+00:00
-- url     : https://prove2.me/theorems/975afe09-fae6-4b16-8efc-b21914394eee
-- title:
--   Weighted Global Seed Coefficient Budget: seed coefficient polynomial
-- statement:
--   The complete real per-seed coefficient is polynomial in digit length,
--   uniformly over every prefix. No signed target or hash call is unit-cost.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L45-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L45-L65

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSeedCoefficientBudget
open WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalSeedCoefficientBudget.seed_coefficient_polynomial (K p B A : ℕ) :
    ∃ C d : ℕ, ∀J j, j≤J→
      seedCoefficient K J p B (A*(p+1)^j) j≤C*(J+1)^d := by sorry
