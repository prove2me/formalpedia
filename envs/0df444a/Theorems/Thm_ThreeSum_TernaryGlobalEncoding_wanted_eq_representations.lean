-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_wanted_eq_representations
-- name    : ThreeSum.TernaryGlobalEncoding.wanted_eq_representations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:59.016217+00:00
-- url     : https://prove2.me/theorems/5b5b5e47-cbe6-4d86-83c9-0f6bd398100e
-- title:
--   Ternary Global Encoding: wanted eq representations
-- statement:
--   Every original modular triple's entire pair-representation fiber is
--   in the wanted-output dictionary.  Quotient carries remain the Radix recursion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L98-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L98-L112

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

theorem ThreeSum.TernaryGlobalEncoding.wanted_eq_representations (hp : p ≠ 0) (J : ℕ) (a b c : ℤ)
    (htriple : (p : ℤ)^J ∣ a+b-c) :
    wantedRepresentations maps occ edge J a b c = representations maps occ edge J (-a) b := by sorry
