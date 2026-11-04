-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawLeft_abs_bound
-- name    : ThreeSum.TernaryGlobalEncoding.rawLeft_abs_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:57:57.153201+00:00
-- url     : https://prove2.me/theorems/50ca971f-4be0-4979-8f37-5620183bba3f
-- title:
--   Ternary Global Encoding: raw Left abs bound
-- statement:
--   The Ternary Global Encoding construction uses the raw Left abs bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L187-L191
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L187-L191

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

theorem ThreeSum.TernaryGlobalEncoding.rawLeft_abs_bound (c : Ω) :
    |rawLeft maps occ edge c| ≤ ((2*L+1)*p : ℕ) := by sorry
