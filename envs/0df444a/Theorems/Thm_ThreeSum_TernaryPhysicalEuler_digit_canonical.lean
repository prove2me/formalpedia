-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_digit_canonical
-- name    : ThreeSum.TernaryPhysicalEuler.digit_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:47.303664+00:00
-- url     : https://prove2.me/theorems/a3486e87-30d2-408b-876f-a07824b2d675
-- title:
--   Ternary Physical Euler: digit canonical
-- statement:
--   The Ternary Physical Euler construction uses the digit canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L42-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L42-L45

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryPhysicalEuler.digit_canonical {N : ℕ} (R : TritWord N) (i : Fin N) :
    LightTernaryPredecessor.digit N (LightTernaryEulerMetadata.lowAt N i.val)
      (LightTernaryEulerMetadata.highAt N i.val) (address R)=(R i).val := by sorry
