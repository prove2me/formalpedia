-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_setup_meets
-- name    : ThreeSum.LightIrreducibleFinder.setup_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:41.985807+00:00
-- url     : https://prove2.me/theorems/31f00856-d80d-4dcb-b3d0-95b0e80e67dc
-- title:
--   Light Irreducible Finder: setup meets
-- statement:
--   The Light Irreducible Finder construction uses the setup meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L331-L389
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L331-L389

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

theorem ThreeSum.LightIrreducibleFinder.setup_meets (C : Layout) [Fact C.p.Prime] {q ctx T depth : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+12<lim.depth)
    (B : Budget lim C q ctx T) (hq : q=C.p^C.dim) :
    Meets lim program 15 depth [C.p,C.dim,q,C.powers,C.target,ctx,C.left,C.right] μ
      (setupTime C q T)
      (fun r ν => ∃ c<q, r=(c+1 : ℕ) ∧ Irreducible (monicOfCode (p := C.p) C.dim c) ∧
        (∀ i<2*C.dim, ν (C.target+i)=(codeDigits (p := C.p) (c+q) i : ℤ)) ∧
        (∀ i≤2*C.dim, ν (C.powers+i)=((C.p^i : ℕ) : ℤ)) ∧ Kept μ ν C.powers) := by sorry
