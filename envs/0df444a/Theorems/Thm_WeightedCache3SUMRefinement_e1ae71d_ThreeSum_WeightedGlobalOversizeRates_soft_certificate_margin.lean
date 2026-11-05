-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeRates_soft_certificate_margin
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeRates.soft_certificate_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:08:42.784719+00:00
-- url     : https://prove2.me/theorems/628fa5fd-2571-4653-804e-ec872a1fc787
-- title:
--   soft_certificate_margin
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryOversizeRates.lean#L187-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryOversizeRates.lean#L187-L188

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeRates
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeRates.soft_certificate_margin : targetExponent-softCertificate=(1/6250000000000 : ℝ) := by sorry
