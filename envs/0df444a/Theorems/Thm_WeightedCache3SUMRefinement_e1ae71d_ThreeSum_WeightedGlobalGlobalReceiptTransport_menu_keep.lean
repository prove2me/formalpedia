-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalGlobalReceiptTransport_menu_keep
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport.menu_keep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:21.67484+00:00
-- url     : https://prove2.me/theorems/bce40fd5-1b29-4d02-90bb-a9a5690d303c
-- title:
--   menu_keep
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryGlobalReceiptTransport.lean#L22-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryGlobalReceiptTransport.lean#L22-L29

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalReceiptTransport
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
open Light LightWeightedGlobalGlobalPrelude LightWeightedGlobalFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport.menu_keep {p : ℕ} [Fact p.Prime] {base d q J c cut : ℕ} {μ ν : ℕ→ℤ}
    (H : LightWeightedGlobalGlobalPreludeProof.Menu μ base d p q J c)
    (K : Kept μ ν cut) (hend : physical base d q J+q*q*(J+2)≤cut) :
    LightWeightedGlobalGlobalPreludeProof.Menu ν base d p q J c := by sorry
