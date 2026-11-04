-- Prove2me | Theorems.Thm_ThreeSum_TernaryGlobalEncoding_localFiber_hash_iff
-- name    : ThreeSum.TernaryGlobalEncoding.localFiber_hash_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:52.570279+00:00
-- url     : https://prove2.me/theorems/ad351fab-efc5-4835-a584-a67e54c11767
-- title:
--   Ternary Global Encoding: local Fiber hash iff
-- statement:
--   The Ternary Global Encoding construction uses the local Fiber hash iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L72-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryGlobalEncoding.lean#L72-L87

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

theorem ThreeSum.TernaryGlobalEncoding.localFiber_hash_iff (a b : ℤ) (c : Ω) :
    c ∈ Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b ↔
      leftHash (maps (occ c)) (edge c) = (-a : ZMod p) ∧
      rightHash (maps (occ c)) (edge c) = (b : ZMod p) := by sorry
