-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalComputedExtensionMenu_coefficient_read
-- name    : ThreeSum.WeightedGlobalComputedExtensionMenu.coefficient_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:53:38.886631+00:00
-- url     : https://prove2.me/theorems/5c8e7ec4-1883-4245-931f-2a8639b11602
-- title:
--   Weighted Global Computed Extension Menu: coefficient read
-- statement:
--   The literal q² menu read is the exact coefficient of the corresponding
--   proof-level field pair, including the physical digit-coordinate reversal.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryComputedExtensionMenu.lean#L48-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryComputedExtensionMenu.lean#L48-L64

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

theorem ThreeSum.WeightedGlobalComputedExtensionMenu.coefficient_read {base J : ℕ} (hd : 0<d) (μ : ℕ→ℤ)
    (H : LightWeightedGlobalGlobalPreludeProof.Menu μ base d p (p^d) J c)
    (ordinal : ℕ) (ho : ordinal<(p^d)*(p^d)) (k : ℕ) (hk : k<J+2) :
    μ (physical base d (p^d) J+ordinal*(J+2)+k)=
      ((TernaryOriginalRowMenu.seedRow (J+2) (functional (p:=p) (c:=c) hd)
        (WeightedGlobalArenaFamilyBudget.seedAt (seeds (p:=p) (d:=d) (c:=c)) ordinal)
        (digitOrder J ⟨k,hk⟩)).val : ℤ) := by sorry
