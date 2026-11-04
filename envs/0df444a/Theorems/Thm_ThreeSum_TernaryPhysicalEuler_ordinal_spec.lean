-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_ordinal_spec
-- name    : ThreeSum.TernaryPhysicalEuler.ordinal_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:36.538398+00:00
-- url     : https://prove2.me/theorems/65be603b-ff33-4c76-8239-cfd473b71fd8
-- title:
--   Ternary Physical Euler: ordinal spec
-- statement:
--   The Ternary Physical Euler construction uses the ordinal spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L19-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L19-L23

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

theorem ThreeSum.TernaryPhysicalEuler.ordinal_spec {N : ℕ} {words : ℕ → TritWord N} {n : ℕ} {w : TritWord N}
    (h : ∃ j<n, words j=w) : ordinal words n w<n ∧ words (ordinal words n w)=w := by sorry
