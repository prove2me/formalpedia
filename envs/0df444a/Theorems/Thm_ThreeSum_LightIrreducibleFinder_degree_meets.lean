-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_degree_meets
-- name    : ThreeSum.LightIrreducibleFinder.degree_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:30.21272+00:00
-- url     : https://prove2.me/theorems/f4f9a74a-f3ce-47ca-bbd1-4ce0cfb9819c
-- title:
--   Light Irreducible Finder: degree meets
-- statement:
--   The Light Irreducible Finder construction uses the degree meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L72-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L72-L153

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

theorem ThreeSum.LightIrreducibleFinder.degree_meets (C : Layout) {q ctx T depth : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+8<lim.depth)
    (hq : 0<q) (hp : 1<C.p) (hdim : 0<C.dim)
    (hctx : ctx+7≤C.left) (hpowCtx : C.powers+(2*C.dim+1)≤ctx)
    (htargetCtx : C.target+2*C.dim≤ctx)
    (hleft : C.left+2*C.dim≤C.right) (hspace : C.right+2*C.dim≤lim.space)
    (hpowRead : ∀ i≤2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i<2*C.dim, μ (C.target+i)=(f i : ℤ))
    (hword : ∀ e, 0<e → e<C.dim → (LightExtensionFactorPredicate.word (atDegree C e) q q : ℤ)≤lim.word)
    (hsearchWord : ((q*q+q+ctx+20 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((C.p+C.dim+q+ctx+32 : ℕ) : ℤ)≤lim.word)
    (htime : ∀ e, 0<e → e<C.dim → factorTime C q e≤T) :
    Meets lim program 10 depth [C.p,C.dim,q,ctx,C.powers,C.target,C.left,C.right] μ (degreeTime C.dim T)
      (fun r ν => r=(degreeFlag C q f (C.dim-1) : ℤ) ∧ Kept μ ν ctx) := by sorry
