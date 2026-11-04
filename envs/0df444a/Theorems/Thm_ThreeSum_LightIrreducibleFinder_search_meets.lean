-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_search_meets
-- name    : ThreeSum.LightIrreducibleFinder.search_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:36.598342+00:00
-- url     : https://prove2.me/theorems/a531767c-76d8-43a6-b179-6f87d45ab77b
-- title:
--   Light Irreducible Finder: search meets
-- statement:
--   The Light Irreducible Finder construction uses the search meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L262-L312
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L262-L312

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light ThreeSum.LightExtensionFactorPredicate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits}
open TernaryExtensionEncoding

theorem ThreeSum.LightIrreducibleFinder.search_meets (C : Layout) {q ctx T depth : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+11<lim.depth)
    (B : Budget lim C q ctx T)
    (hpowRead : ∀ i≤2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ)) :
    Meets lim program 13 depth [C.p,C.dim,q,C.powers,C.target,ctx,C.left,C.right] μ
      (searchTime C q T)
      (fun r ν => r=(chosen C q q : ℤ) ∧ Kept μ ν C.target) := by sorry
