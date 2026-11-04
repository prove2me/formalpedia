-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_original_position_cover_and_cap
-- name    : ThreeSum.TernaryGlobalEncoding.original_position_cover_and_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:56.606024+00:00
-- url     : https://prove2.me/theorems/ea346c5f-6c81-4f4d-9b2d-8e227903eb4d
-- title:
--   Ternary Global Encoding: original position cover and cap
-- statement:
--   Covers arbitrary original integer positions, including repeated equal
--   values, with positive representation multiplicity and the exact radix cap.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L116-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L116-L136

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

theorem ThreeSum.TernaryGlobalEncoding.original_position_cover_and_cap {A B C : Type*}
    (leftInput : A → ℤ) (rightInput : B → ℤ) (outputInput : C → ℤ)
    (hp : p ≠ 0) (cap : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ c : Ω,
      leftHash (maps (occ c)) (edge c) = a ∧ rightHash (maps (occ c)) (edge c) = b)
    (hcap : ∀ a b : ℤ,
      (Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b).card ≤ cap)
    (J : ℕ) (i : A) (j : B) (k : C)
    (htriple : (p : ℤ)^J ∣ leftInput i+rightInput j-outputInput k) :
    1 ≤ (wantedRepresentations maps occ edge J (leftInput i) (rightInput j) (outputInput k)).card ∧
    (wantedRepresentations maps occ edge J (leftInput i) (rightInput j) (outputInput k)).card ≤ cap^J := by sorry
