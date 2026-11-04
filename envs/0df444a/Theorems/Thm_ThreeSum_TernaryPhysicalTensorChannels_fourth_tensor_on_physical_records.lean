-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalTensorChannels_fourth_tensor_on_physical_records
-- name    : ThreeSum.TernaryPhysicalTensorChannels.fourth_tensor_on_physical_records
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:51.658087+00:00
-- url     : https://prove2.me/theorems/7046bcc2-459e-42c1-9105-5e1eeaa0dc3f
-- title:
--   Ternary Physical Tensor Channels: fourth tensor on physical records
-- statement:
--   The Ternary Physical Tensor Channels construction uses the fourth tensor on physical records property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalTensorChannels.lean#L36-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalTensorChannels.lean#L36-L46

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalTensorChannels
open Finset TernaryJointType TernaryWeightedPhysicalSources TernaryWeightChannels
open scoped BigOperators
variable {ι κ I : Type*}

theorem ThreeSum.TernaryPhysicalTensorChannels.fourth_tensor_on_physical_records {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (L : ι→I→ℤ) (R : κ→I→ℤ) (a b c d : I) (Q : TritWord N) :
    TernaryConvolution.convolution
      (histogram S left (productWeight L a b))
      (histogram T right (productWeight R c d)) Q=
      TernaryPairedTensor.tensor (fun x : records S T left right Q => L x.val.1)
        (fun x : records S T left right Q => R x.val.2) a b c d := by sorry
