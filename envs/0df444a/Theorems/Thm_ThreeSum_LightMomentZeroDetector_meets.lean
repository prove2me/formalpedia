-- Prove2me | Theorems.Thm_ThreeSum_LightMomentZeroDetector_meets
-- name    : ThreeSum.LightMomentZeroDetector.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:48:19.756744+00:00
-- url     : https://prove2.me/theorems/25cae1ea-4f6f-48b3-b4f6-442069789830
-- title:
--   Light Moment Zero Detector: meets
-- statement:
--   The Light Moment Zero Detector construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L82-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L82-L97

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector

theorem ThreeSum.LightMomentZeroDetector.meets (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hv : Function.Injective v) (hweights : ∀ s, w s≠0)
    (ht : t≤H) {lim : Limits} {P : Program} {p depth : ℕ}
    (hp : P[p]?=some (body (atoms H) H))
    (hspace : base+(2*H+1)≤lim.space) (hspaceWord : (lim.space : ℤ)≤lim.word)
    (U : ℤ) (hU : 0≤U) (ha : |a|≤U)
    (hword : wordBound U H≤lim.word)
    (hmabs : ∀ k≤2*H, |μ (base+k)|≤U)
    (hm : ∀ k≤2*H, μ (base+k)=moment v w k) :
    Meets lim P p depth [base,a] μ (time (atoms H) H)
      (fun r ν => r=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ ν=μ) := by sorry
