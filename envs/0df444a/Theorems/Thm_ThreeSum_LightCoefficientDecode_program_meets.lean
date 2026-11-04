-- Prove2me | Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
-- name    : ThreeSum.LightCoefficientDecode.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:19.291836+00:00
-- url     : https://prove2.me/theorems/eae2d2a9-9ee8-43da-9556-6916087d92df
-- title:
--   Light Coefficient Decode: program meets
-- statement:
--   The Light Coefficient Decode construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoefficientDecode.lean#L117-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoefficientDecode.lean#L117-L129

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoefficientDecode
open Light
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoefficientDecode.program_meets
    {μ : ℕ → ℤ} {W p k powers start stride dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hp : 1 ≤ p)
    (hspace : dst+n ≤ lim.space) (hpowers : powers+(W+1) ≤ lim.space)
    (hsep : Apart powers (W+1) dst n)
    (hword : (word W p k start stride : ℤ) ≤ lim.word)
    (hcoords : ∀ i < n, start+stride*i < W)
    (hread : ∀ e ≤ W, μ (powers+e) = ((p^e : ℕ) : ℤ)) :
    Meets lim program 0 d [W,p,k,powers,start,stride,dst,n] μ (time n k)
      (fun _ μ' =>
        (∀ i < n, μ' (dst+i) = (digit p k (start+stride*i) : ℤ)) ∧
        SameOutside μ μ' dst n) := by sorry
