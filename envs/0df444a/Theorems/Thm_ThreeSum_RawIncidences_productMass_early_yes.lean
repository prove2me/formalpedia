-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_productMass_early_yes
-- name    : ThreeSum.RawIncidences.productMass_early_yes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:49.592974+00:00
-- url     : https://prove2.me/theorems/4b9e9241-d4ad-4946-ada0-06080304f41b
-- title:
--   Raw Incidences: product Mass early yes
-- statement:
--   The same stopping rule stated directly for the product-weight mass
--   computed for one band of A, B and C indices.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L451-L469
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L451-L469

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

theorem ThreeSum.RawIncidences.productMass_early_yes {h J : ℕ} {P d : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (aux : Finset ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hsep : ∀ t ∈ A ×ˢ (B ×ˢ C), difference a b c t ≠ 0 →
      ∃ l ∈ aux, ¬l ∣ difference a b c t)
    (hlarge : representationCap h J *
      Arithmetic.weightedFalseCount (A ×ˢ (B ×ˢ C)) (difference a b c) aux P <
        productMass h J P d A B C a b c) :
    ∃ i ∈ A, ∃ j ∈ B, ∃ k ∈ C, a i + b j = c k := by sorry
