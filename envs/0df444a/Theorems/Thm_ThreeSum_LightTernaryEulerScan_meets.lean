-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
-- name    : ThreeSum.LightTernaryEulerScan.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:33:50.646906+00:00
-- url     : https://prove2.me/theorems/096f7aa3-5904-4bf4-8fc7-3d2bd7908eeb
-- title:
--   Light Ternary Euler Scan: meets
-- statement:
--   This contract requires physical metadata and exact Euler numerators.
--   The row computation is the fully specified four-procedure arithmetic kernel,
--   not an oracle call. Its read addresses may span bank and prior memo layers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerScan.lean#L83-L199
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerScan.lean#L83-L199

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerScan
open Light
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryEulerScan.meets {pMain pFill pRow pSum pDivide pNaturalDivide N rows ws ks ranks vals current h pcount fr U V : ℕ}
    (hmain : P[pMain]?=some (body pFill))
    (hfill : P[pFill]?=some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]?=some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]?=some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]?=some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]?=some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (weights keys : ℕ → ℕ → ℕ) (g f : ℕ → ℤ) (rank : ℕ → ℕ)
    (F : Light.Emod.Pre lim (current-h) V fr) (hh : h ≤ current)
    (hws : ws+N*rows ≤ vals) (hks : ks+N*rows ≤ vals) (hranks : ranks+rows ≤ vals)
    (hvals : vals+rows ≤ fr) (hspace : pcount ≤ lim.space)
    (hrankRead : ∀ j < rows, μ (ranks+j)=(rank j : ℤ))
    (hweights : ∀ j < rows, ∀ i < N, μ (ws+N*j+i)=(weights j i : ℤ))
    (hkeys : ∀ j < rows, ∀ i < N, μ (ks+N*j+i)=(keys j i : ℤ))
    (hrange : ∀ j < rows, ∀ i < N, keys j i < pcount ∧ keys j i < fr)
    (hread : ∀ j < rows, rank j=current → ∀ i < N, μ (keys j i)=g (keys j i))
    (hweight : ∀ j < rows, ∀ i < N, weights j i ≤ 2)
    (hvalue : ∀ j < rows, rank j=current → ∀ i < N, |g (keys j i)| ≤ U)
    (hpre : ∀ j < rows, rank j=current → ∀ i < N, ∀ k < rows,
      rank k=current → keys j i ≠ vals+k)
    (hEuler : ∀ j < rows, rank j=current →
      LightTernaryWeightedSum.sum (weights j) (keys j) g N=(current-h : ℕ)*f j)
    (hV : 2*(N+1)*U ≤ V) (hd : d+4 ≤ lim.depth)
    (hcontrols : ((N+rows+current+h+20 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [N,rows,ws,ks,ranks,vals,current,h,pcount,fr] μ
      (time N rows V)
      (fun r ν => r=0 ∧ Stored μ ν f rank vals current fr rows) := by sorry
