-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumerationMain_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:09:37.889854+00:00
-- url     : https://prove2.me/theorems/bcb8a9e1-7555-4f71-86a9-7cdb38f0a715
-- title:
--   meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightNearEnumerationMain.lean#L22-L225
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightNearEnumerationMain.lean#L22-L225

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumerationMain
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedNearEnumeration ThreeSum.LightWeightedNearEnumeration
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain.meets {pMain pBranch W powers : ℕ}
    (hmain : P[pMain]?=some (body pBranch))
    (hbranch : P[pBranch]?=some (branchBody pMain))
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*W+1)≤lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ)≤lim.word)
    (hcontrol : ((2740*W+3000 : ℕ) : ℤ)≤lim.word) :
    ∀ qs : List ℕ, ∀ D pref dst caps : ℕ, ∀ μ : ℕ→ℤ,
      (∀ q∈qs, q<3) → qs.length≤W → D≤2740*W → pref+4^qs.length≤4^W →
      dst+(words qs D).length≤powers → dst+(words qs D).length≤caps →
      caps+qs.length≤lim.space → Powers μ powers (2*W) →
      Seg μ caps (qs.map (fun q => (digitCost q : ℤ))) →
      ∀ d, d+2*qs.length≤lim.depth →
      Meets lim P pMain d [qs.length,D,pref,dst,powers,caps] μ (time qs D)
        (fun count μ' => count=((words qs D).length : ℤ) ∧
          Seg μ' dst (output qs D pref) ∧ SameOutside μ μ' dst (words qs D).length) := by sorry
