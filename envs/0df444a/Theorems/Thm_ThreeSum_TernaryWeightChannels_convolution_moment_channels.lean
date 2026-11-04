-- Prove2me | Theorems.Thm_ThreeSum_TernaryWeightChannels_convolution_moment_channels
-- name    : ThreeSum.TernaryWeightChannels.convolution_moment_channels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:51.379262+00:00
-- url     : https://prove2.me/theorems/5cd96cce-3bad-48d5-abd0-c8764542dc30
-- title:
--   Ternary Weight Channels: convolution moment channels
-- statement:
--   Shared weighted source banks compute the exact integer moment of the
--   physical pair measure, retaining repeated words and original multiplicity.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L66-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L66-L75

import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators
variable {ι κ I : Type*}

theorem ThreeSum.TernaryWeightChannels.convolution_moment_channels {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : TritWord N) (k : ℕ) :
    (∑ j∈range (k+1), TernaryConvolution.convolution
      (histogram S left (fun i => (leftMoment k j).eval (fun _ => B i)))
      (histogram T right (fun i => (rightMoment k j).eval (fun _ => C i))) Q)=
      ∑ b∈S, ∑ c∈T, if TernaryConvolution.Adds (left b) (right c) Q then
        (C c-B b)^k else 0 := by sorry
