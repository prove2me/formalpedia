-- Prove2me | Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_boundary_le_boundary_add_componentGeneratorDisagreement
-- name    : SoficGroups.KunActualFirstStageReferenceExpansion.boundary_le_boundary_add_componentGeneratorDisagreement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/f6beb533-56e4-446a-9b42-9b0a1e815552
-- title:
--   SoficGroups.KunActualFirstStageReferenceExpansion.boundary_le_boundary_add_componentGeneratorDisagreement
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

theorem SoficGroups.KunActualFirstStageReferenceExpansion.boundary_le_boundary_add_componentGeneratorDisagreement
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σref σact : ι → Equiv.Perm V)
    (C E : Finset V) (hEC : E ⊆ C) :
    SoficGroups.boundary σref E ≤
      SoficGroups.boundary σact E +
        componentGeneratorDisagreement C σref σact := by sorry
