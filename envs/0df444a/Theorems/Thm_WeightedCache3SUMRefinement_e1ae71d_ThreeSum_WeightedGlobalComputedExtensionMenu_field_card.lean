-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalComputedExtensionMenu_field_card
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalComputedExtensionMenu.field_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:27:09.505302+00:00
-- url     : https://prove2.me/theorems/34776c9f-4349-4e11-8104-dc3935f0fb3b
-- title:
--   field_card
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryComputedExtensionMenu.lean#L43-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryComputedExtensionMenu.lean#L43-L44

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryActualSeedEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryComputedExtensionMenu
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalComputedExtensionMenu
open Polynomial TernaryExtensionEncoding LightExtensionBackendLayout
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
variable {d c : ℕ} [Fact (Irreducible (modulus p d c))]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalComputedExtensionMenu.field_card : Fintype.card (AdjoinRoot (modulus p d c))=p^d := by sorry
