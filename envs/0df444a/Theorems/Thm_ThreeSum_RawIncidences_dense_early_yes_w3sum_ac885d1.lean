-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_dense_early_yes_w3sum_ac885d1
-- name    : ThreeSum.RawIncidences.dense_early_yes_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:52.048192+00:00
-- url     : https://prove2.me/theorems/61db5794-c6f2-48b9-9d51-68d3f62cf9b5
-- title:
--   Raw Incidences: dense early yes
-- statement:
--   The dense stopping rule uses the actual guarded incidences and the
--   actual radix multiplicity bound. Its score is the weighted false-count
--   quantity computed by the arithmetic histogram identities.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L403-L433
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L403-L433

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.RawIncidences.dense_early_yes_w3sum_ac885d1 {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (aux : Finset ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hsep : ∀ t ∈ T, difference a b c t ≠ 0 → ∃ l ∈ aux, ¬l ∣ difference a b c t)
    (hlarge : representationCap h J * Arithmetic.weightedFalseCount T (difference a b c) aux P <
      rawMass h J P d T a b c) :
    ∃ t ∈ T, difference a b c t = 0 := by sorry
