-- Prove2me | Theorems.Thm_ThreeSum_TernaryReconstruction_firstCross_eq_frozenInverse
-- name    : ThreeSum.TernaryReconstruction.firstCross_eq_frozenInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:05.998346+00:00
-- url     : https://prove2.me/theorems/53ffa97d-d58f-44b0-b2a4-18e74465287b
-- title:
--   Ternary Reconstruction: first Cross eq frozen Inverse
-- statement:
--   The Ternary Reconstruction construction uses the first Cross eq frozen Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean#L77-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean#L77-L86

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler

theorem ThreeSum.TernaryReconstruction.firstCross_eq_frozenInverse {N : ℕ} (T : ℕ) (H : TritWord N → ℤ)
    (coords : List (Fin N)) (R : TritWord N) :
    firstCross T H coords R = frozenInverse coords H R := by sorry
