-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawOutput_abs_bound
-- name    : ThreeSum.TernaryGlobalEncoding.rawOutput_abs_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:08.959241+00:00
-- url     : https://prove2.me/theorems/31ae5d6e-9bc9-4641-a5c2-c786b38d61ce
-- title:
--   Ternary Global Encoding: raw Output abs bound
-- statement:
--   The Ternary Global Encoding construction uses the raw Output abs bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L205-L215
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L205-L215

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

theorem ThreeSum.TernaryGlobalEncoding.rawOutput_abs_bound (w : Coordinate (Fin L) → ZMod p) (q : TritWord L) :
    |rawOutput w q| ≤ ((2*L+2)*p : ℕ) := by sorry
