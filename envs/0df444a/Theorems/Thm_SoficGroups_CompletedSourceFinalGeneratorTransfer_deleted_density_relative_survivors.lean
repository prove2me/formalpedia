-- Prove2me | Theorems.Thm_SoficGroups_CompletedSourceFinalGeneratorTransfer_deleted_density_relative_survivors
-- name    : SoficGroups.CompletedSourceFinalGeneratorTransfer.deleted_density_relative_survivors
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/7c90e6b2-4803-4e77-92f4-3c356f7c3aff
-- title:
--   SoficGroups.CompletedSourceFinalGeneratorTransfer.deleted_density_relative_survivors
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CompletedSourceChosenWordRestrictionTransfer

theorem SoficGroups.CompletedSourceFinalGeneratorTransfer.deleted_density_relative_survivors
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (D : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Finset.univ \ D n : Finset (V n)).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((D n).card : ℝ) /
          (Finset.univ \ D n : Finset (V n)).card)
      atTop (nhds 0) := by sorry
