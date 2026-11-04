-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_clog_power_upper
-- name    : ThreeSum.WeightedGlobalPrincipalDimensions.clog_power_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:27.992941+00:00
-- url     : https://prove2.me/theorems/7597fafa-88db-4139-ba5c-8977c99f6b35
-- title:
--   Weighted Global Principal Dimensions: clog power upper
-- statement:
--   The Weighted Global Principal Dimensions construction uses the clog power upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L17-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L17-L25

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger

theorem ThreeSum.WeightedGlobalPrincipalDimensions.clog_power_upper {M n : ℕ} (hM : 1 < M) (hn : 1 < n) :
    M^(Nat.clog M (n^2)) ≤ M*n^2 := by sorry
