-- Prove2me | Theorems.Thm_ThreeSum_LightMomentZeroDetector_program_meets
-- name    : ThreeSum.LightMomentZeroDetector.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:33.911202+00:00
-- url     : https://prove2.me/theorems/71dae8f6-f1b2-492e-98d6-770571e10ccd
-- title:
--   Light Moment Zero Detector: program meets
-- statement:
--   The one-procedure program has no hidden initialization or advice.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L100-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L100-L111

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector

theorem ThreeSum.LightMomentZeroDetector.program_meets (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hv : Function.Injective v) (hweights : ∀ s, w s≠0)
    (ht : t≤H) {lim : Limits} {depth : ℕ}
    (hspace : base+(2*H+1)≤lim.space) (hspaceWord : (lim.space : ℤ)≤lim.word)
    (U : ℤ) (hU : 0≤U) (ha : |a|≤U)
    (hword : wordCoefficient H*(U+1)^wordDegree H≤lim.word)
    (hmabs : ∀ k≤2*H, |μ (base+k)|≤U)
    (hm : ∀ k≤2*H, μ (base+k)=moment v w k) :
    Meets lim (program H) 0 depth [base,a] μ (time (atoms H) H)
      (fun r ν => r=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ ν=μ) := by sorry
