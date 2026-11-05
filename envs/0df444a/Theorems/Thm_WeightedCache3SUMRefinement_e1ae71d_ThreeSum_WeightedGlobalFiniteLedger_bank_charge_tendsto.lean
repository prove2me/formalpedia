-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFiniteLedger_bank_charge_tendsto
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger.bank_charge_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:06:02.796525+00:00
-- url     : https://prove2.me/theorems/72ac8b79-f004-47d3-be8e-2cbb5d8cb6cd
-- title:
--   bank_charge_tendsto
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFiniteLedger.lean#L24-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryFiniteLedger.lean#L24-L26

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFiniteLedger.bank_charge_tendsto :
    Tendsto bankCharge atTop (𝓝 (2*bankEntropy/Hpi)) := by sorry
