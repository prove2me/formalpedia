-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_candidate_meets
-- name    : ThreeSum.LightIrreducibleFinder.candidate_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:36.338539+00:00
-- url     : https://prove2.me/theorems/89c3d22f-3540-4d0d-8c8c-d95cf1453c40
-- title:
--   Light Irreducible Finder: candidate meets
-- statement:
--   The Light Irreducible Finder construction uses the candidate meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L209-L247
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L209-L247

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

theorem ThreeSum.LightIrreducibleFinder.candidate_meets (C : Layout) {c q ctx T depth : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+10<lim.depth)
    (B : Budget lim C q ctx T) (hc : c<q)
    (hpowRead : ∀ i≤2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ)) :
    Meets lim program 12 depth [c,C.p,C.dim,q,C.powers,C.target,ctx,C.left,C.right] μ
      (candidateTime C q T)
      (fun r ν => r=(degreeFlag C q (LightCoefficientDecode.digit C.p (c+q)) (C.dim-1) : ℤ) ∧
        Kept μ ν C.target) := by sorry
