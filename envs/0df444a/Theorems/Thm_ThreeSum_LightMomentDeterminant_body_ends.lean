-- Prove2me | Theorems.Thm_ThreeSum_LightMomentDeterminant_body_ends
-- name    : ThreeSum.LightMomentDeterminant.body_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:49:48.251891+00:00
-- url     : https://prove2.me/theorems/68e6ce9c-6269-449b-b04f-c1c21f59c02f
-- title:
--   Light Moment Determinant: body ends
-- statement:
--   The Light Moment Determinant construction uses the body ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L131-L195
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L131-L195

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators
open FiniteMomentZeroDetector

theorem ThreeSum.LightMomentDeterminant.body_ends (h : ℕ) {t : ℕ} (v w : Fin t → ℤ) (a : ℤ)
    (hv : Function.Injective v) (hw : ∀ s, w s≠0) (hth : t≤h)
    (atoms : ℕ → Expr) (σ : State) {lim : Limits} {P : Program} {d : ℕ}
    (U : ℤ) (hU : 0≤U)
    (hs : ∀ i, (atoms i).Safe lim σ)
    (hx : ∀ i, |(atoms i).val σ|≤U)
    (hword : wordBound U h≤lim.word)
    (hlead : ∀ k≤h, (leading k).eval (fun i => (atoms i).val σ)=(hankel v w k).det)
    (hmod : ∀ k≤h, (modified k).eval (fun i => (atoms i).val σ)=(modifiedHankel v w a k).det) :
    Ends lim P d (body atoms h) σ (time atoms h)
      (fun τ => τ.loc 0=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ τ.mem=σ.mem) := by sorry
