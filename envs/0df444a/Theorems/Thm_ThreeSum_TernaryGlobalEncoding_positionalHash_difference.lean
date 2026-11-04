-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_positionalHash_difference
-- name    : ThreeSum.TernaryGlobalEncoding.positionalHash_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:48.087282+00:00
-- url     : https://prove2.me/theorems/4965746d-8f05-4965-8074-2ede8d6ddd34
-- title:
--   Ternary Global Encoding: positional Hash difference
-- statement:
--   The Ternary Global Encoding construction uses the positional Hash difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L61-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L61-L70

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

theorem ThreeSum.TernaryGlobalEncoding.positionalHash_difference (xs : List Ω) :
    Radix.positionalHash (p : ℤ) (rawRight maps occ edge) xs-
      Radix.positionalHash (p : ℤ) (rawLeft maps occ edge) xs =
    Radix.positionalHash (p : ℤ) (blockKey maps) (xs.map (blockOfChoice occ edge)) := by sorry
