-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSeedCoefficientBudget_hash_linear
-- name    : ThreeSum.WeightedGlobalSeedCoefficientBudget.hash_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:13:12.84801+00:00
-- url     : https://prove2.me/theorems/482bef85-dfae-48f8-8c21-1f5f0596aaca
-- title:
--   Weighted Global Seed Coefficient Budget: hash linear
-- statement:
--   The actual signed row hash has linear digit-length cost at fixed
--   native prime and signed digit bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L18-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L18-L23

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSeedCoefficientBudget
open WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalSeedCoefficientBudget.hash_linear (J p B : ℕ) :
    LightSignedRowHash.time (J+2) p B+120≤
      (596+80*p*(p+B))*(J+1) := by sorry
