-- Prove2me | Theorems.Thm_SoficGroups_KunActualSelectedCentralizerFiniteModel_trackedCompletedAlmostCentralizer_separated
-- name    : SoficGroups.KunActualSelectedCentralizerFiniteModel.trackedCompletedAlmostCentralizer_separated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/2aead7f3-c0e4-49bf-bf5c-6f865de85d79
-- title:
--   SoficGroups.KunActualSelectedCentralizerFiniteModel.trackedCompletedAlmostCentralizer_separated
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSelectedCentralizerFiniteModel
open Filter Topology

theorem SoficGroups.KunActualSelectedCentralizerFiniteModel.trackedCompletedAlmostCentralizer_separated
    {V ι J : Type} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V)
    (p : J → Equiv.Perm V)
    (F : Finset J) (t : ℕ)
    (hdefect : ∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
      SoficGroups.permutationCommutationDefect σ (p j) ≤ t)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card V < 5 * SoficGroups.permutationDistance (p x) (p y)) :
    ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card V <
        5 * SoficGroups.permutationDistance
          (trackedCompletedAlmostCentralizer
            σ p F t hdefect x).permutation
          (trackedCompletedAlmostCentralizer
            σ p F t hdefect y).permutation := by sorry
