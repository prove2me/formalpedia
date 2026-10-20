-- Prove2me | Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_exists_vanishing_completedRestriction_additive_expansion_of_selected_bad
-- name    : SoficGroups.KunActualFirstStageReferenceExpansion.exists_vanishing_completedRestriction_additive_expansion_of_selected_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/af88a0da-3599-438d-843b-22f75c7dbac7
-- title:
--   SoficGroups.KunActualFirstStageReferenceExpansion.exists_vanishing_completedRestriction_additive_expansion_of_selected_bad
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunActualFirstStageReferenceExpansion.exists_vanishing_completedRestriction_additive_expansion_of_selected_bad
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (C B : (n : ℕ) → Finset (V n))
    (hC : ∀ n, (C n).Nonempty)
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (γ : ℝ)
    (hexpand : ∀ n, ∀ E : Finset (V n), E ⊆ C n →
      2 * E.card ≤ (C n).card →
        γ * (E.card : ℝ) ≤
          (SoficGroups.boundary (σref n) E : ℝ))
    (hbad : ∀ n i (x : V n), x ∈ C n →
      σref n i x ≠ σact n i x → x ∈ B n)
    (hboundary : Tendsto
      (fun n =>
        (SoficGroups.boundary (σref n) (C n) : ℝ) /
          (C n).card)
      atTop (nhds 0))
    (hbad_density : Tendsto
      (fun n =>
        (((C n ∩ B n).card : ℝ) / (C n).card))
      atTop (nhds 0)) :
    ∃ a : ℕ → ℝ,
      (∀ n, 0 ≤ a n) ∧
      Tendsto a atTop (nhds 0) ∧
      ∀ n, ∀ E : Finset {x : V n // x ∈ C n},
        γ * min (E.card : ℝ)
          ((Fintype.card {x : V n // x ∈ C n} : ℝ) - E.card) -
            a n * Fintype.card {x : V n // x ∈ C n} ≤
          (SoficGroups.boundary
            (fun i =>
              SoficGroups.MatchedComponentCompletion.completedRestriction
                (σact n i) (C n)) E : ℝ) := by sorry
