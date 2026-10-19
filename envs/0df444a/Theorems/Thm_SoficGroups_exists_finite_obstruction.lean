-- Prove2me | Theorems.Thm_SoficGroups_exists_finite_obstruction
-- name    : SoficGroups.exists_finite_obstruction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/a4153884-ba59-4b64-bb1e-32bf784a828c
-- title:
--   SoficGroups.exists_finite_obstruction
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.exists_finite_obstruction {G : Type*} [Group G] (hG : ¬ Sofic G) :
    ∃ (F : Finset G) (ε : ℝ), 1 ∈ F ∧ 0 < ε ∧ ε < 1 ∧
      ∀ M : PermutationModel G, ¬ GoodOn M F ε := by sorry
