-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_physical_bank
-- name    : ThreeSum.TernaryPhysicalEuler.physical_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:59:12.519652+00:00
-- url     : https://prove2.me/theorems/368808c4-e9a8-4123-9fab-b1ebb0023aa0
-- title:
--   Ternary Physical Euler: physical bank
-- statement:
--   The Ternary Physical Euler construction uses the physical bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L33-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L33-L36

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

theorem ThreeSum.TernaryPhysicalEuler.physical_bank {N bv nv nb j : ℕ} (bankWords nearWords : ℕ → TritWord N)
    (hsep : bv+nb≤nv) (hj : j<nb) :
    physicalWord bankWords nearWords bv nv (bv+j)=bankWords j := by sorry
