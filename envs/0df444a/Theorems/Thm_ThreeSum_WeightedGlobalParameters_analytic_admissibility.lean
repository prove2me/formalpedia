-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_analytic_admissibility
-- name    : ThreeSum.WeightedGlobalParameters.analytic_admissibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:42.280941+00:00
-- url     : https://prove2.me/theorems/4c15bea5-0726-413a-ad3a-be6068a0477f
-- title:
--   Weighted Global Parameters: analytic admissibility
-- statement:
--   The Weighted Global Parameters construction uses the analytic admissibility property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L179-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L179-L188

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.analytic_admissibility :
    0 < bankEntropy ∧ 0 < queryEntropy ∧ partitionEntropy < Hpi ∧
    Halpha < bankEntropy ∧ (Hpi + partitionEntropy) / 2 < Halpha ∧
    0 < Hpi - partitionEntropy + 2 * queryEntropy := by sorry
