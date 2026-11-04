-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalComputedExtensionMenu_field_card
-- name    : ThreeSum.WeightedGlobalComputedExtensionMenu.field_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:01:02.433484+00:00
-- url     : https://prove2.me/theorems/ca65e950-7a3e-46bc-9ff4-84801f514c8a
-- title:
--   Weighted Global Computed Extension Menu: field card
-- statement:
--   The Weighted Global Computed Extension Menu construction uses the field card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryComputedExtensionMenu.lean#L43-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryComputedExtensionMenu.lean#L43-L44

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryActualSeedEnumeration
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalComputedExtensionMenu
open Polynomial TernaryExtensionEncoding LightExtensionBackendLayout
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
variable {d c : ℕ} [Fact (Irreducible (modulus p d c))]

theorem ThreeSum.WeightedGlobalComputedExtensionMenu.field_card : Fintype.card (AdjoinRoot (modulus p d c))=p^d := by sorry
