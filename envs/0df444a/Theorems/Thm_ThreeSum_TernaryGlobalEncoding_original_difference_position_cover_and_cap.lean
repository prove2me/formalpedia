-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_original_difference_position_cover_and_cap
-- name    : ThreeSum.TernaryGlobalEncoding.original_difference_position_cover_and_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:57:55.186931+00:00
-- url     : https://prove2.me/theorems/8eff4bd0-ff6f-45ea-8bc5-9e16530e7079
-- title:
--   Ternary Global Encoding: original difference position cover and cap
-- statement:
--   The baseline source lookup keeps the original `b,c` labels.  Its
--   negative raw left key is matched at native hash `-b`; the wanted key is `a`.
--   The arithmetic failure class remains the original difference `c-b-a`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L142-L155
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L142-L155

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

theorem ThreeSum.TernaryGlobalEncoding.original_difference_position_cover_and_cap {A B C : Type*}
    (aInput : A → ℤ) (bInput : B → ℤ) (cInput : C → ℤ)
    (hp : p ≠ 0) (cap : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ c : Ω,
      leftHash (maps (occ c)) (edge c) = a ∧ rightHash (maps (occ c)) (edge c) = b)
    (hcap : ∀ a b : ℤ,
      (Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b).card ≤ cap)
    (J : ℕ) (i : A) (j : B) (k : C)
    (htriple : (p : ℤ)^J ∣ cInput k-bInput j-aInput i) :
    1 ≤ (wantedRepresentations maps occ edge J (-bInput j) (cInput k) (aInput i)).card ∧
    (wantedRepresentations maps occ edge J (-bInput j) (cInput k) (aInput i)).card ≤ cap^J := by sorry
