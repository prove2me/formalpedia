-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawSource_upper
-- name    : ThreeSum.TernaryGlobalEncoding.rawSource_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:44.861553+00:00
-- url     : https://prove2.me/theorems/779f9b65-f479-4ca2-bfcc-3f57c6ee0bfa
-- title:
--   Ternary Global Encoding: raw Source upper
-- statement:
--   The Ternary Global Encoding construction uses the raw Source upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L178-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L178-L185

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

theorem ThreeSum.TernaryGlobalEncoding.rawSource_upper (w : Coordinate (Fin L) → ZMod p) (tag : Bool) (a : TritWord L) :
    rawSource w tag a ≤ ((2*L+1)*p : ℕ) := by sorry
