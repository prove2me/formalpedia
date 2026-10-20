-- Prove2me | Theorems.Thm_SoficGroups_KunActualSelectedCentralizerFiniteModel_nonempty_expandingCentralizerFiniteModel_of_selected_completed_sequence
-- name    : SoficGroups.KunActualSelectedCentralizerFiniteModel.nonempty_expandingCentralizerFiniteModel_of_selected_completed_sequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/96a01423-f7b8-4e09-af38-01dcf7500f79
-- title:
--   SoficGroups.KunActualSelectedCentralizerFiniteModel.nonempty_expandingCentralizerFiniteModel_of_selected_completed_sequence
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSelectedCentralizerFiniteModel
open Filter Topology

theorem SoficGroups.KunActualSelectedCentralizerFiniteModel.nonempty_expandingCentralizerFiniteModel_of_selected_completed_sequence
    {J : Type} [Group J] (F : Finset J)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (ι : Type) [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (hp : ∀ n, p n 1 = 1)
    (t : ℕ → ℕ)
    (h : ℝ) (hpositive : 0 < h)
    (hdefect : ∀ᶠ n in atTop,
      ∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
        SoficGroups.permutationCommutationDefect
          (σ n) (p n j) ≤ t n)
    (hexp : ∀ᶠ n in atTop, ∀ E : Finset (V n),
      h * min (E.card : ℝ)
        ((Fintype.card (V n) : ℝ) - E.card) ≤
          (SoficGroups.boundary (σ n) E : ℝ))
    (hsmall : ∀ᶠ n in atTop,
      (10 : ℝ) * t n < h * Fintype.card (V n))
    (himprove : ∀ᶠ n in atTop,
      SoficGroups.HasAlmostCentralizerImprovement (σ n) (t n))
    (hmul : ∀ᶠ n in atTop, ∀ x ∈ F, ∀ y ∈ F,
      5 * SoficGroups.permutationDistance
        (p n (x * y)) (p n x * p n y) ≤ Fintype.card (V n))
    (hsep : ∀ᶠ n in atTop, ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card (V n) <
        5 * SoficGroups.permutationDistance (p n x) (p n y)) :
    Nonempty (SoficGroups.ExpandingCentralizerFiniteModel J F) := by sorry
