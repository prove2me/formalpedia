-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawSource_cast_right
-- name    : ThreeSum.TernaryGlobalEncoding.rawSource_cast_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:49.329559+00:00
-- url     : https://prove2.me/theorems/e0db7f50-1c74-4cbd-8e3e-eeac5807acc2
-- title:
--   Ternary Global Encoding: raw Source cast right
-- statement:
--   The Ternary Global Encoding construction uses the raw Source cast right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L30-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L30-L32

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

theorem ThreeSum.TernaryGlobalEncoding.rawSource_cast_right (w : Coordinate (Fin L) → ZMod p) (e : LocalEdge L α π) :
    (rawSource w true (right e) : ZMod p) = rightHash w e := by sorry
