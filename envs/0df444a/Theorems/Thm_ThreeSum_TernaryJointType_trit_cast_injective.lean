-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_trit_cast_injective
-- name    : ThreeSum.TernaryJointType.trit_cast_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:29:57.346193+00:00
-- url     : https://prove2.me/theorems/a548e25c-bf83-4a1f-a888-0503b830d3c5
-- title:
--   Ternary Joint Type: trit cast injective
-- statement:
--   The Ternary Joint Type construction uses the trit cast injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L172-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L172-L179

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset

theorem ThreeSum.TernaryJointType.trit_cast_injective {p : ℕ} (hp : 2 < p) :
    Function.Injective (fun x : Fin 3 => (x.val : ZMod p)) := by sorry
