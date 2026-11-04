-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalComputedExtensionMenu_functional_ne_zero
-- name    : ThreeSum.WeightedGlobalComputedExtensionMenu.functional_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:54:11.743811+00:00
-- url     : https://prove2.me/theorems/45e82542-6444-4ba8-96a1-fa65549c56e8
-- title:
--   Weighted Global Computed Extension Menu: functional ne zero
-- statement:
--   The Weighted Global Computed Extension Menu construction uses the functional ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryComputedExtensionMenu.lean#L40-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryComputedExtensionMenu.lean#L40-L41

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

theorem ThreeSum.WeightedGlobalComputedExtensionMenu.functional_ne_zero (hd : 0<d) : (functional (p:=p) (c:=c) hd)≠0 := by sorry
