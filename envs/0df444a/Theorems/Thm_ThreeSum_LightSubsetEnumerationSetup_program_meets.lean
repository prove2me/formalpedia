-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
-- name    : ThreeSum.LightSubsetEnumerationSetup.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:42:53.503562+00:00
-- url     : https://prove2.me/theorems/e6799592-224e-4f29-add5-5f7da26088d4
-- title:
--   Light Subset Enumeration Setup: program meets
-- statement:
--   The Light Subset Enumeration Setup construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetEnumerationSetup.lean#L70-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetEnumerationSetup.lean#L70-L80

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSubsetEnumerationSetup.program_meets {μ : ℕ → ℤ} {L k dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hk : k ≤ L+1) (hdst : dst+L.choose k ≤ work)
    (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [L,k,dst,work] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        SegN μ' dst (enumerateLayer L k) ∧ Powers μ' work L ∧
        KeptBut μ μ' work dst (L.choose k)) := by sorry
