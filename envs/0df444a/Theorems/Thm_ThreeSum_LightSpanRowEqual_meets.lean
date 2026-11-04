-- Prove2me | Theorems.Thm_ThreeSum_LightSpanRowEqual_meets
-- name    : ThreeSum.LightSpanRowEqual.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:46.27011+00:00
-- url     : https://prove2.me/theorems/ec965125-2cf0-4b21-b4fc-7864b3cb57f0
-- title:
--   Light Span Row Equal: meets
-- statement:
--   The Light Span Row Equal construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogTest.lean#L30-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogTest.lean#L30-L67

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
open ThreeSum ThreeSum.LightSpanRowEqual
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSpanRowEqual.meets {pMain a b J d : ℕ} (hmain : P[pMain]?=some body)
    (μ : ℕ → ℤ) (f g : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+J≤lim.space) (hb : b+J≤lim.space) (hone : (1 : ℤ)≤lim.word)
    (hf : ∀ i<J, |f i|≤lim.word) (hg : ∀ i<J, |g i|≤lim.word)
    (hreadA : ∀ i<J, μ (a+i)=f i) (hreadB : ∀ i<J, μ (b+i)=g i) :
    Meets lim P pMain d [a,b,J] μ (time J)
      (fun r ν => r=(flag f g J : ℤ) ∧ ν=μ) := by sorry
