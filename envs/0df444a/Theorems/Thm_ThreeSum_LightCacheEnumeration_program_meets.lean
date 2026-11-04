-- Prove2me | Theorems.Thm_ThreeSum_LightCacheEnumeration_program_meets
-- name    : ThreeSum.LightCacheEnumeration.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:43:07.576803+00:00
-- url     : https://prove2.me/theorems/f87615b1-b876-4e24-9bc8-54ffb5102623
-- title:
--   Light Cache Enumeration: program meets
-- statement:
--   The Light Cache Enumeration construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L273-L284
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L273-L284

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_LightEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightCacheEnumeration.program_meets {W powers N T pref dst d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*W+1) ≤ lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((1025*W+1100 : ℕ) : ℤ) ≤ lim.word)
    (hN : N ≤ W) (hT : T ≤ 1025*W) (hprefix : pref+4^N ≤ 4^W)
    (hdst : dst+(codes N T).length ≤ powers) (hpowers : Powers μ powers (2*W))
    (hd : d+N ≤ lim.depth) :
    Meets lim program 0 d [N,T,pref,dst,powers] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst (output N T pref) ∧ SameOutside μ μ' dst (codes N T).length) := by sorry
