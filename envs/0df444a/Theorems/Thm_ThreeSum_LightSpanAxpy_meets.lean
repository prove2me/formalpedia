-- Prove2me | Theorems.Thm_ThreeSum_LightSpanAxpy_meets
-- name    : ThreeSum.LightSpanAxpy.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:36:48.851783+00:00
-- url     : https://prove2.me/theorems/77582379-def5-432e-b245-a77a7a868b96
-- title:
--   Light Span Axpy: meets
-- statement:
--   The Light Span Axpy construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanAxpy.lean#L26-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanAxpy.lean#L26-L76

import Definitions.Def_Submission_ThreeSum_LightPrimeCoefficient
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightSpanAxpy
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightTernaryPass_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSpanAxpy
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSpanAxpy.meets {pMain pMulAdd pDivide src rowBase dst J a p d : ℕ}
    (hmain : P[pMain]?=some (body pMulAdd))
    (hmul : P[pMulAdd]?=some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f row : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+J≤dst) (hrow : rowBase+J≤dst)
    (hdst : dst+J≤lim.space) (hp : 0<p) (ha : a<p)
    (hword : (LightPrimeCoefficient.word p : ℤ)≤lim.word)
    (hf : ∀ i<J, f i<p) (hr : ∀ i<J, row i<p)
    (hread : ∀ i<J, μ (src+i)=(f i : ℤ))
    (hreadRow : ∀ i<J, μ (rowBase+i)=(row i : ℤ))
    (hd : d+2≤lim.depth) :
    Meets lim P pMain d [src,rowBase,dst,J,a,p] μ (time J p)
      (fun _ ν => (∀ i<J, ν (dst+i)=values f row a p i) ∧ SameOutside μ ν dst J) := by sorry
