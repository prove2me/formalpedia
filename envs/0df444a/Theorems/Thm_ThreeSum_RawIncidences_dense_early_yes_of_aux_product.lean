-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_dense_early_yes_of_aux_product
-- name    : ThreeSum.RawIncidences.dense_early_yes_of_aux_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:46.654194+00:00
-- url     : https://prove2.me/theorems/9d9316c5-c87a-438f-b1c1-0d3247d86097
-- title:
--   Raw Incidences: dense early yes of aux product
-- statement:
--   The Raw Incidences construction uses the dense early yes of aux product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L435-L447
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L435-L447

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

theorem ThreeSum.RawIncidences.dense_early_yes_of_aux_product {h J : ℕ} {P d : ℤ}
    (T : Finset (Original α β γ)) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (aux : Finset ℤ) (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hcop : (aux : Set ℤ).Pairwise (fun l r => IsCoprime l r))
    (hbound : ∀ t ∈ T, difference a b c t ≠ 0 →
      (difference a b c t).natAbs < (∏ l ∈ aux, l).natAbs)
    (hlarge : representationCap h J * Arithmetic.weightedFalseCount T (difference a b c) aux P <
      rawMass h J P d T a b c) :
    ∃ t ∈ T, difference a b c t = 0 := by sorry
