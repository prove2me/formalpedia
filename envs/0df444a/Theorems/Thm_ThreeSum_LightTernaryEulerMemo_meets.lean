-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
-- name    : ThreeSum.LightTernaryEulerMemo.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:43:54.80635+00:00
-- url     : https://prove2.me/theorems/ac2a12e7-e48e-4831-9018-35d9b85512e6
-- title:
--   Light Ternary Euler Memo: meets
-- statement:
--   The Light Ternary Euler Memo construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMemo.lean#L57-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMemo.lean#L57-L174

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerMemo
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryEulerMemo.meets {pMain pScan pFill pRow pSum pDivide pNaturalDivide N rows ws ks ranks vals T h maxRank pcount fr U V : ℕ}
    (hmain : P[pMain]?=some (body pScan))
    (hscan : P[pScan]?=some (LightTernaryEulerScan.body pFill))
    (hfill : P[pFill]?=some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]?=some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]?=some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]?=some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]?=some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (weights keys : ℕ → ℕ → ℕ) (g f : ℕ → ℤ) (rank : ℕ → ℕ)
    (F : ∀ current, T<current → current≤maxRank → Light.Emod.Pre lim (current-h) V fr)
    (hT : T≤maxRank) (hh : h≤T)
    (hws : ws+N*rows ≤ vals) (hks : ks+N*rows ≤ vals) (hranks : ranks+rows ≤ vals)
    (hvals : vals+rows ≤ fr) (hspace : pcount ≤ lim.space)
    (hrankRead : ∀ j < rows, μ (ranks+j)=(rank j : ℤ))
    (hrankRange : ∀ j < rows, T<rank j ∧ rank j≤maxRank)
    (hweights : ∀ j < rows, ∀ i < N, μ (ws+N*j+i)=(weights j i : ℤ))
    (hkeys : ∀ j < rows, ∀ i < N, μ (ks+N*j+i)=(keys j i : ℤ))
    (hrange : ∀ j < rows, ∀ i < N, keys j i < pcount ∧ keys j i < fr)
    (hbank : ∀ j < rows, ∀ i < N, keys j i<vals → μ (keys j i)=g (keys j i))
    (hmemo : ∀ j < rows, g (vals+j)=f j)
    (hweight : ∀ j < rows, ∀ i < N, weights j i ≤ 2)
    (hvalue : ∀ j < rows, ∀ i < N, |g (keys j i)| ≤ U)
    (hpre : ∀ j < rows, ∀ i < N,
      keys j i<vals ∨ ∃ k<rows, keys j i=vals+k ∧ rank k<rank j)
    (hEuler : ∀ j < rows,
      LightTernaryWeightedSum.sum (weights j) (keys j) g N=(rank j-h : ℕ)*f j)
    (hV : 2*(N+1)*U ≤ V) (hd : d+5 ≤ lim.depth)
    (hword : ((N+rows+maxRank+h+20 : ℕ) : ℤ) ≤ lim.word)
    (hw : (lim.space : ℤ) ≤ lim.word) (hfr : fr≤lim.space) :
    Meets lim P pMain d [N,rows,ws,ks,ranks,vals,T,h,maxRank,pcount,fr] μ
      (time N rows (maxRank-T) V)
      (fun r ν => r=0 ∧ Kept μ ν vals ∧ ∀ j<rows, ν (vals+j)=f j) := by sorry
