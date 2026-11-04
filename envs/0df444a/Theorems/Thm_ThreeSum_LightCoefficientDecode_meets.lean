-- Prove2me | Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
-- name    : ThreeSum.LightCoefficientDecode.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:34.180451+00:00
-- url     : https://prove2.me/theorems/20ef8c46-b64b-4a2a-abf2-3ccb259b737c
-- title:
--   Light Coefficient Decode: meets
-- statement:
--   The Light Coefficient Decode construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoefficientDecode.lean#L38-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoefficientDecode.lean#L38-L113

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoefficientDecode
open Light
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoefficientDecode.meets {pMain pDigit pDivide : ℕ}
    (hmain : P[pMain]? = some (body pDigit))
    (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body)
    {μ : ℕ → ℤ} {W p k powers start stride dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hp : 1 ≤ p)
    (hspace : dst+n ≤ lim.space) (hpowers : powers+(W+1) ≤ lim.space)
    (hsep : Apart powers (W+1) dst n)
    (hword : (word W p k start stride : ℤ) ≤ lim.word)
    (hcoords : ∀ i < n, start+stride*i < W)
    (hread : ∀ e ≤ W, μ (powers+e) = ((p^e : ℕ) : ℤ)) :
    Meets lim P pMain d [W,p,k,powers,start,stride,dst,n] μ (time n k)
      (fun _ μ' =>
        (∀ i < n, μ' (dst+i) = (digit p k (start+stride*i) : ℤ)) ∧
        SameOutside μ μ' dst n) := by sorry
