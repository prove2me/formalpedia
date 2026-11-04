-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalTensorChannels_sum_records
-- name    : ThreeSum.TernaryPhysicalTensorChannels.sum_records
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:45:21.110797+00:00
-- url     : https://prove2.me/theorems/3d9431fc-a279-4b21-afc7-ca16578046c2
-- title:
--   Ternary Physical Tensor Channels: sum records
-- statement:
--   The Ternary Physical Tensor Channels construction uses the sum records property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalTensorChannels.lean#L17-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalTensorChannels.lean#L17-L24

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalTensorChannels
open Finset TernaryJointType TernaryWeightedPhysicalSources TernaryWeightChannels
open scoped BigOperators
variable {ι κ I : Type*}

theorem ThreeSum.TernaryPhysicalTensorChannels.sum_records {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N) (Q : TritWord N) (F : ι×κ→ℤ) :
    (∑ x : records S T left right Q, F x.val)=
      ∑ i∈S, ∑ j∈T, if TernaryConvolution.Adds (left i) (right j) Q then F (i,j) else 0 := by sorry
