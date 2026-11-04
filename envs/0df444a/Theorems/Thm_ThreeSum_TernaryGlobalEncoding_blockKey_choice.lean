-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_blockKey_choice
-- name    : ThreeSum.TernaryGlobalEncoding.blockKey_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:47.545164+00:00
-- url     : https://prove2.me/theorems/f68a1a2a-76cc-497e-b782-816ba9d2c5dc
-- title:
--   Ternary Global Encoding: block Key choice
-- statement:
--   The Ternary Global Encoding construction uses the block Key choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L56-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L56-L59

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

theorem ThreeSum.TernaryGlobalEncoding.blockKey_choice (c : Ω) :
    blockKey maps (blockOfChoice occ edge c) = rawRight maps occ edge c-rawLeft maps occ edge c := by sorry
