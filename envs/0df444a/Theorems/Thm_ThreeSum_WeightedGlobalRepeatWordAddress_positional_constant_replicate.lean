-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalRepeatWordAddress_positional_constant_replicate
-- name    : ThreeSum.WeightedGlobalRepeatWordAddress.positional_constant_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:20:59.841547+00:00
-- url     : https://prove2.me/theorems/40c79180-4686-448d-a4bc-7ccc9a9f35c1
-- title:
--   Weighted Global Repeat Word Address: positional constant replicate
-- statement:
--   The Weighted Global Repeat Word Address construction uses the positional constant replicate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatWordAddress.lean#L23-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatWordAddress.lean#L23-L28

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatWordAddress
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalRepeatWordAddress
open ThreeSum.LightTernaryRepeatWord
open TernaryJointType
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalRepeatWordAddress.positional_constant_replicate {A : Type*} (x : A) (q b : ℤ) (r : ℕ) :
    Radix.positionalHash b (fun _ : A=>q) (List.replicate r x)=
      Radix.positionalHash b (fun y : ℤ=>y) (List.replicate r q) := by sorry
