-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_raw_addition
-- name    : ThreeSum.TernaryGlobalEncoding.raw_addition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:50.535814+00:00
-- url     : https://prove2.me/theorems/1667bca5-ca13-4766-a696-c0e3d2dd1118
-- title:
--   Ternary Global Encoding: raw addition
-- statement:
--   The Ternary Global Encoding construction uses the raw addition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L34-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L34-L46

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

theorem ThreeSum.TernaryGlobalEncoding.raw_addition (w : Coordinate (Fin L) → ZMod p) (e : LocalEdge L α π) :
    rawSource w false (left e)+rawSource w true (right e) = rawOutput w (output e) := by sorry
