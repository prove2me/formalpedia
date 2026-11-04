-- Prove2me | Theorems.Thm_ThreeSum_LightWeightRow_program_meets
-- name    : ThreeSum.LightWeightRow.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:16.612888+00:00
-- url     : https://prove2.me/theorems/7307b75b-45ec-4ebf-88df-928617a015e0
-- title:
--   Light Weight Row: program meets
-- statement:
--   The Light Weight Row construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightRow.lean#L118-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightRow.lean#L118-L130

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightRow
open Light
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWeightRow.program_meets
    {μ : ℕ → ℤ} {W p k powers start stride dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hp : 1 ≤ p)
    (hspace : dst+n ≤ lim.space) (hpowers : powers+(W+1) ≤ lim.space)
    (hsep : Apart powers (W+1) dst n)
    (hword : (word W p k start stride : ℤ) ≤ lim.word)
    (hcoords : ∀ i < n, start+stride*i < W)
    (hread : ∀ e ≤ W, μ (powers+e) = ((p^e : ℕ) : ℤ)) :
    Meets lim program 0 d [W,p,k,powers,start,stride,dst,n] μ (time n k)
      (fun _ μ' =>
        (∀ i < n, μ' (dst+i) = (WeightEnumeration.digit p W k (start+stride*i) : ℤ)) ∧
        SameOutside μ μ' dst n) := by sorry
