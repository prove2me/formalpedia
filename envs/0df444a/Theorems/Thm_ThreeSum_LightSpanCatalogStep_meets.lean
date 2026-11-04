-- Prove2me | Theorems.Thm_ThreeSum_LightSpanCatalogStep_meets
-- name    : ThreeSum.LightSpanCatalogStep.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:22.405194+00:00
-- url     : https://prove2.me/theorems/4b461bc0-f56b-43f8-a5a7-66b4410c78bb
-- title:
--   Light Span Catalog Step: meets
-- statement:
--   The Light Span Catalog Step construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogStep.lean#L102-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogStep.lean#L102-L179

import Definitions.Def_Submission_ThreeSum_LightSpanAxpy
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSpanAxpy_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSpanCatalogStep
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSpanCatalogStep.meets {pMain pBlock pAxpy pMulAdd pDivide src n rowBase dst J p d : ℕ}
    (hmain : P[pMain]?=some (body pBlock))
    (hblock : P[pBlock]?=some (LightSpanCatalogBlock.body pAxpy))
    (haxpy : P[pAxpy]?=some (LightSpanAxpy.body pMulAdd))
    (hmul : P[pMulAdd]?=some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+J*n≤dst) (hrow : rowBase+J≤dst)
    (hdst : dst+J*n*p≤lim.space) (hp : 0<p)
    (hword : (LightPrimeCoefficient.word p : ℤ)≤lim.word)
    (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word)
    (hf : ∀ k<n, ∀ i<J, f k i<p) (hr : ∀ i<J, row i<p)
    (hread : ∀ k<n, ∀ i<J, μ (src+J*k+i)=(f k i : ℤ))
    (hreadRow : ∀ i<J, μ (rowBase+i)=(row i : ℤ))
    (hd : d+4≤lim.depth) :
    Meets lim P pMain d [src,n,rowBase,dst,J,p] μ (time J p n)
      (fun _ ν => (∀ u<p, ∀ k<n, ∀ i<J, ν (dst+J*n*u+J*k+i)=LightSpanAxpy.values (f k) row u p i) ∧
        SameOutside μ ν dst (J*n*p)) := by sorry
