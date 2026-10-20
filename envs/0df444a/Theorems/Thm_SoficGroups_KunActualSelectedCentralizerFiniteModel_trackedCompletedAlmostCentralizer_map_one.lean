-- Prove2me | Theorems.Thm_SoficGroups_KunActualSelectedCentralizerFiniteModel_trackedCompletedAlmostCentralizer_map_one
-- name    : SoficGroups.KunActualSelectedCentralizerFiniteModel.trackedCompletedAlmostCentralizer_map_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/ccefa8e3-bd23-4791-bb43-5f922e3949fe
-- title:
--   SoficGroups.KunActualSelectedCentralizerFiniteModel.trackedCompletedAlmostCentralizer_map_one
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSelectedCentralizerFiniteModel
open Filter Topology

theorem SoficGroups.KunActualSelectedCentralizerFiniteModel.trackedCompletedAlmostCentralizer_map_one
    {V ι J : Type} [Fintype V] [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V)
    (p : J → Equiv.Perm V)
    (hp : p 1 = 1)
    (F : Finset J) (t : ℕ)
    (hdefect : ∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
      SoficGroups.permutationCommutationDefect σ (p j) ≤ t) :
    (trackedCompletedAlmostCentralizer σ p F t hdefect 1).permutation = 1 := by sorry
