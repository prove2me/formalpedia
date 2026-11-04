-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_digit_canonical
-- name    : ThreeSum.WeightedPhysicalEuler.digit_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:18.173809+00:00
-- url     : https://prove2.me/theorems/fc4ef3c0-edf8-4aee-a5cf-5e0facf2fcf1
-- title:
--   Weighted Physical Euler: digit canonical
-- statement:
--   The Weighted Physical Euler construction uses the digit canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L48-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L48-L51

import Definitions.Def_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_Weighted_PhysicalEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedPhysicalEuler.digit_canonical {N : ℕ} (R : TritWord N) (i : Fin N) :
    LightWeightedPredecessor.digit N (LightWeightedEulerMetadata.lowAt N i.val)
      (LightWeightedEulerMetadata.highAt N i.val) (address R)=(R i).val := by sorry
