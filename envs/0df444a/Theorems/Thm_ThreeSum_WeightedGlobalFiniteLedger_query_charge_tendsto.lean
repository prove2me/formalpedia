-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_query_charge_tendsto
-- name    : ThreeSum.WeightedGlobalFiniteLedger.query_charge_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:51:28.52142+00:00
-- url     : https://prove2.me/theorems/6d880370-73c4-442f-8111-585e45adb458
-- title:
--   Weighted Global Finite Ledger: query charge tendsto
-- statement:
--   The Weighted Global Finite Ledger construction uses the query charge tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFiniteLedger.lean#L28-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFiniteLedger.lean#L28-L36

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology

theorem ThreeSum.WeightedGlobalFiniteLedger.query_charge_tendsto :
    Tendsto queryCharge atTop (𝓝 (2-partitionEntropy/Hpi+2*queryEntropy/Hpi)) := by sorry
