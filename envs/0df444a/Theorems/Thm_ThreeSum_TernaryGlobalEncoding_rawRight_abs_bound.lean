-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawRight_abs_bound
-- name    : ThreeSum.TernaryGlobalEncoding.rawRight_abs_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:57:58.754466+00:00
-- url     : https://prove2.me/theorems/e7bc2184-8c92-466a-bdeb-7f77c26cda9c
-- title:
--   Ternary Global Encoding: raw Right abs bound
-- statement:
--   The Ternary Global Encoding construction uses the raw Right abs bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L193-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L193-L197

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

theorem ThreeSum.TernaryGlobalEncoding.rawRight_abs_bound (c : Ω) :
    |rawRight maps occ edge c| ≤ ((2*L+1)*p : ℕ) := by sorry
