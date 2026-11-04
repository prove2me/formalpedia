-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawSource_cast_left
-- name    : ThreeSum.TernaryGlobalEncoding.rawSource_cast_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:46.891033+00:00
-- url     : https://prove2.me/theorems/f38dfc85-7d9f-47b5-ba58-95eec0c68972
-- title:
--   Ternary Global Encoding: raw Source cast left
-- statement:
--   The Ternary Global Encoding construction uses the raw Source cast left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L26-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L26-L28

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryGlobalEncoding
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq Ω]
variable (maps : I → Coordinate (Fin L) → ZMod p) (occ : Ω → I)
  (edge : Ω → LocalEdge L α π)

theorem ThreeSum.TernaryGlobalEncoding.rawSource_cast_left (w : Coordinate (Fin L) → ZMod p) (e : LocalEdge L α π) :
    (rawSource w false (left e) : ZMod p) = leftHash w e := by sorry
