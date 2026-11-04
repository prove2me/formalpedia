-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalTensorChannels_moment_on_physical_records
-- name    : ThreeSum.TernaryPhysicalTensorChannels.moment_on_physical_records
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:45.370007+00:00
-- url     : https://prove2.me/theorems/c8fc0d58-b51d-4919-ac83-5d1c5442185c
-- title:
--   Ternary Physical Tensor Channels: moment on physical records
-- statement:
--   The Ternary Physical Tensor Channels construction uses the moment on physical records property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalTensorChannels.lean#L26-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalTensorChannels.lean#L26-L34

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalTensorChannels
open Finset TernaryJointType TernaryWeightedPhysicalSources TernaryWeightChannels
open scoped BigOperators
variable {ι κ I : Type*}

theorem ThreeSum.TernaryPhysicalTensorChannels.moment_on_physical_records {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : TritWord N) (k : ℕ) :
    (∑ j∈range (k+1), TernaryConvolution.convolution
      (histogram S left (fun i => (leftMoment k j).eval (fun _ => B i)))
      (histogram T right (fun i => (rightMoment k j).eval (fun _ => C i))) Q)=
      ∑ x : records S T left right Q, (C x.val.2-B x.val.1)^k := by sorry
