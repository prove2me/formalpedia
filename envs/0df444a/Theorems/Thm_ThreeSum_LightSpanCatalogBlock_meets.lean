-- Prove2me | Theorems.Thm_ThreeSum_LightSpanCatalogBlock_meets
-- name    : ThreeSum.LightSpanCatalogBlock.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:34.233928+00:00
-- url     : https://prove2.me/theorems/8e6f67b4-3a7b-45a1-b04d-93f9b34f54b2
-- title:
--   Light Span Catalog Block: meets
-- statement:
--   The Light Span Catalog Block construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogStep.lean#L22-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogStep.lean#L22-L80

import Definitions.Def_Submission_ThreeSum_LightSpanAxpy
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSpanAxpy_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSpanCatalogBlock
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSpanCatalogBlock.meets {pMain pAxpy pMulAdd pDivide src n rowBase dst J a p d : ℕ}
    (hmain : P[pMain]?=some (body pAxpy))
    (haxpy : P[pAxpy]?=some (LightSpanAxpy.body pMulAdd))
    (hmul : P[pMulAdd]?=some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+J*n≤dst) (hrow : rowBase+J≤dst)
    (hdst : dst+J*n≤lim.space) (hp : 0<p) (ha : a<p)
    (hword : (LightPrimeCoefficient.word p : ℤ)≤lim.word)
    (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word)
    (hf : ∀ k<n, ∀ i<J, f k i<p) (hr : ∀ i<J, row i<p)
    (hread : ∀ k<n, ∀ i<J, μ (src+J*k+i)=(f k i : ℤ))
    (hreadRow : ∀ i<J, μ (rowBase+i)=(row i : ℤ))
    (hd : d+3≤lim.depth) :
    Meets lim P pMain d [src,n,rowBase,dst,J,a,p] μ (time J p n)
      (fun _ ν => (∀ k<n, ∀ i<J, ν (dst+J*k+i)=LightSpanAxpy.values (f k) row a p i) ∧ SameOutside μ ν dst (J*n)) := by sorry
