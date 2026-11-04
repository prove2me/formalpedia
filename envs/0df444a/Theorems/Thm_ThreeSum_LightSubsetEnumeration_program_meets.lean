-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
-- name    : ThreeSum.LightSubsetEnumeration.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:34.353004+00:00
-- url     : https://prove2.me/theorems/7d721720-91fa-458d-992b-85e13cce6d52
-- title:
--   Light Subset Enumeration: program meets
-- statement:
--   The Light Subset Enumeration construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetEnumeration.lean#L207-L217
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetEnumeration.lean#L207-L217

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSubsetEnumeration.program_meets {W powers L k pref dst d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hL : L ≤ W) (hk : k ≤ W+1) (hprefix : pref+2^L ≤ 2^W)
    (hdst : dst+L.choose k ≤ powers) (hpowers : Powers μ powers W)
    (hd : d+L ≤ lim.depth) :
    Meets lim program 0 d [L,k,pref,dst,powers] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        Seg μ' dst (output L k pref) ∧ SameOutside μ μ' dst (L.choose k)) := by sorry
