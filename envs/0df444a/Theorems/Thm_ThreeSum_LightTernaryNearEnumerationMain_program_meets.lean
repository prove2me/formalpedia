-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_program_meets
-- name    : ThreeSum.LightTernaryNearEnumerationMain.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:48.134277+00:00
-- url     : https://prove2.me/theorems/131d489e-98a2-455a-bbc1-4b18f930f5b1
-- title:
--   Light Ternary Near Enumeration Main: program meets
-- statement:
--   The Light Ternary Near Enumeration Main construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumerationMain.lean#L219-L234
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumerationMain.lean#L219-L234

import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration ThreeSum.LightTernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearEnumerationMain.program_meets {W powers D pref dst caps d : ℕ} {qs : List ℕ} {μ : ℕ→ℤ}
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*W+1)≤lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ)≤lim.word)
    (hqs : ∀ q∈qs, q<3) (hN : qs.length≤W) (hD : D≤2*W)
    (hprefix : pref+4^qs.length≤4^W)
    (hdstP : dst+(words qs D).length≤powers)
    (hdstC : dst+(words qs D).length≤caps) (hcspace : caps+qs.length≤lim.space)
    (hpowers : Powers μ powers (2*W)) (hcaps : Seg μ caps (qs.map (fun q => (q : ℤ))))
    (hd : d+2*qs.length≤lim.depth) :
    Meets lim LightTernaryNearEnumeration.program 0 d
      [qs.length,D,pref,dst,powers,caps] μ (time qs D)
      (fun count μ' => count=((words qs D).length : ℤ) ∧
        Seg μ' dst (output qs D pref) ∧ SameOutside μ μ' dst (words qs D).length) := by sorry
