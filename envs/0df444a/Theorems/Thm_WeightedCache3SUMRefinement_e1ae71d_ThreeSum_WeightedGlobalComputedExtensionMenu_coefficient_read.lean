-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalComputedExtensionMenu_coefficient_read
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalComputedExtensionMenu.coefficient_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:25.556944+00:00
-- url     : https://prove2.me/theorems/6717adb1-1cc3-4e8d-a7c1-13db64f40feb
-- title:
--   coefficient_read
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryComputedExtensionMenu.lean#L48-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryComputedExtensionMenu.lean#L48-L64

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalComputedExtensionMenu.coefficient_read {base J : ℕ} (hd : 0<d) (μ : ℕ→ℤ)
    (H : LightWeightedGlobalGlobalPreludeProof.Menu μ base d p (p^d) J c)
    (ordinal : ℕ) (ho : ordinal<(p^d)*(p^d)) (k : ℕ) (hk : k<J+2) :
    μ (physical base d (p^d) J+ordinal*(J+2)+k)=
      ((TernaryOriginalRowMenu.seedRow (J+2) (functional (p:=p) (c:=c) hd)
        (WeightedGlobalArenaFamilyBudget.seedAt (seeds (p:=p) (d:=d) (c:=c)) ordinal)
        (digitOrder J ⟨k,hk⟩)).val : ℤ) := by sorry
