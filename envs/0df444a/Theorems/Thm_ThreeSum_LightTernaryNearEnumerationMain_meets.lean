-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_meets
-- name    : ThreeSum.LightTernaryNearEnumerationMain.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:49.816503+00:00
-- url     : https://prove2.me/theorems/93249fd1-3957-4ef7-ac18-def2ac68e0b2
-- title:
--   Light Ternary Near Enumeration Main: meets
-- statement:
--   The Light Ternary Near Enumeration Main construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumerationMain.lean#L15-L217
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumerationMain.lean#L15-L217

import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration ThreeSum.LightTernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearEnumerationMain.meets {pMain pBranch W powers : ℕ}
    (hmain : P[pMain]?=some (body pBranch))
    (hbranch : P[pBranch]?=some (branchBody pMain))
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*W+1)≤lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ)≤lim.word) :
    ∀ qs : List ℕ, ∀ D pref dst caps : ℕ, ∀ μ : ℕ→ℤ,
      (∀ q∈qs, q<3) → qs.length≤W → D≤2*W → pref+4^qs.length≤4^W →
      dst+(words qs D).length≤powers → dst+(words qs D).length≤caps →
      caps+qs.length≤lim.space → Powers μ powers (2*W) →
      Seg μ caps (qs.map (fun q => (q : ℤ))) →
      ∀ d, d+2*qs.length≤lim.depth →
      Meets lim P pMain d [qs.length,D,pref,dst,powers,caps] μ (time qs D)
        (fun count μ' => count=((words qs D).length : ℤ) ∧
          Seg μ' dst (output qs D pref) ∧ SameOutside μ μ' dst (words qs D).length) := by sorry
