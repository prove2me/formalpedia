-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets
-- name    : ThreeSum.LightWeightedNearEnumerationMain.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:35.919465+00:00
-- url     : https://prove2.me/theorems/47acd477-167c-4a00-a8dd-0ffa6ef6debb
-- title:
--   Light Weighted Near Enumeration Main: program meets
-- statement:
--   The Light Weighted Near Enumeration Main construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumerationMain.lean#L227-L243
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumerationMain.lean#L227-L243

import Definitions.Def_Submission_Weighted_LightNearEnumeration
import Definitions.Def_Submission_Weighted_LightNearEnumerationMain
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedNearEnumeration ThreeSum.LightWeightedNearEnumeration
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedNearEnumerationMain.program_meets {W powers D pref dst caps d : ℕ} {qs : List ℕ} {μ : ℕ→ℤ}
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*W+1)≤lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ)≤lim.word)
    (hcontrol : ((1025*W+1100 : ℕ) : ℤ)≤lim.word)
    (hqs : ∀ q∈qs, q<3) (hN : qs.length≤W) (hD : D≤1025*W)
    (hprefix : pref+4^qs.length≤4^W)
    (hdstP : dst+(words qs D).length≤powers)
    (hdstC : dst+(words qs D).length≤caps) (hcspace : caps+qs.length≤lim.space)
    (hpowers : Powers μ powers (2*W)) (hcaps : Seg μ caps (qs.map (fun q => (digitCost q : ℤ))))
    (hd : d+2*qs.length≤lim.depth) :
    Meets lim LightWeightedNearEnumeration.program 0 d
      [qs.length,D,pref,dst,powers,caps] μ (time qs D)
      (fun count μ' => count=((words qs D).length : ℤ) ∧
        Seg μ' dst (output qs D pref) ∧ SameOutside μ μ' dst (words qs D).length) := by sorry
