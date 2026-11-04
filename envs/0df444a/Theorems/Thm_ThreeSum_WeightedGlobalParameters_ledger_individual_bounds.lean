-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_ledger_individual_bounds
-- name    : ThreeSum.WeightedGlobalParameters.ledger_individual_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:06:49.579238+00:00
-- url     : https://prove2.me/theorems/d83ec2dc-3595-4fdc-b0ef-f01910fdaca1
-- title:
--   Weighted Global Parameters: ledger individual bounds
-- statement:
--   The Weighted Global Parameters construction uses the ledger individual bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L215-L238
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L215-L238

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.ledger_individual_bounds :
    2*bankEntropy/Hpi<certificateExponent ∧
    2-partitionEntropy/Hpi+2*queryEntropy/Hpi<certificateExponent ∧
    2*Halpha/Hpi<certificateExponent ∧
    1+partitionEntropy/Hpi<certificateExponent ∧
    2-partitionEntropy/Hpi<certificateExponent := by sorry
