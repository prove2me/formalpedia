-- Prove2me | Theorems.Thm_ThreeSum_TernaryMomentSchedule_scaled_physical_moments
-- name    : ThreeSum.TernaryMomentSchedule.scaled_physical_moments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:48.238897+00:00
-- url     : https://prove2.me/theorems/58bb4bb4-2262-4680-af3f-24d1e653f8d8
-- title:
--   Ternary Moment Schedule: scaled physical moments
-- statement:
--   The Ternary Moment Schedule construction uses the scaled physical moments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L81-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMomentSchedule.lean#L81-L95

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentSchedule
open Finset TernaryJointType
open scoped BigOperators

theorem ThreeSum.TernaryMomentSchedule.scaled_physical_moments {ι κ : Type*} {N : ℕ}
    (S : Finset ι) (T : Finset κ) (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : ℕ→TritWord N) (scale : ℕ→ℤ)
    (terms k i : ℕ) (hk : k<terms) :
    aggregate (channels terms)
      (fun k j i => scale i*TernaryConvolution.convolution
        (TernaryWeightedPhysicalSources.histogram S left
          (fun b => (TernaryWeightChannels.leftMoment k j).eval (fun _ => B b)))
        (TernaryWeightedPhysicalSources.histogram T right
          (fun c => (TernaryWeightChannels.rightMoment k j).eval (fun _ => C c))) (Q i)) k i=
      scale i*∑ b∈S, ∑ c∈T,
        if TernaryConvolution.Adds (left b) (right c) (Q i) then (C c-B b)^k else 0 := by sorry
