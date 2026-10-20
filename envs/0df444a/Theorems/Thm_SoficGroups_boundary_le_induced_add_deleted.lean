-- Prove2me | Theorems.Thm_SoficGroups_boundary_le_induced_add_deleted
-- name    : SoficGroups.boundary_le_induced_add_deleted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/617b0d1e-f1f4-4b87-85c7-60759d6c3c48
-- title:
--   SoficGroups.boundary_le_induced_add_deleted
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

theorem SoficGroups.boundary_le_induced_add_deleted {V ι : Type*}
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) :
    boundary σ E ≤ inducedBoundary σ B E + Fintype.card ι * B.card := by sorry
