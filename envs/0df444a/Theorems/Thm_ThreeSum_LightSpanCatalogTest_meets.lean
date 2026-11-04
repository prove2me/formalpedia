-- Prove2me | Theorems.Thm_ThreeSum_LightSpanCatalogTest_meets
-- name    : ThreeSum.LightSpanCatalogTest.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:50.587877+00:00
-- url     : https://prove2.me/theorems/595e8c6f-c803-4af5-af59-7d0567b25a36
-- title:
--   Light Span Catalog Test: meets
-- statement:
--   The Light Span Catalog Test construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogTest.lean#L107-L176
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogTest.lean#L107-L176

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSpanAxpy_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogBlock_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogStep_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightSpanCatalogTest
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSpanCatalogTest.meets {pMain pEq catalog n J candidate d : ℕ}
    (hmain : P[pMain]?=some (body pEq)) (heq : P[pEq]?=some LightSpanRowEqual.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hcat : catalog+J*n≤lim.space) (hrow : candidate+J≤lim.space)
    (hone : (1 : ℤ)≤lim.word) (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word)
    (hf : ∀ k<n, ∀ i<J, |f k i|≤lim.word) (hr : ∀ i<J, |row i|≤lim.word)
    (hread : ∀ k<n, ∀ i<J, μ (catalog+J*k+i)=f k i)
    (hreadRow : ∀ i<J, μ (candidate+i)=row i) (hd : d+1≤lim.depth) :
    Meets lim P pMain d [catalog,n,J,candidate] μ (time J n)
      (fun r ν => r=(flag f row J n : ℤ) ∧ ν=μ) := by sorry
