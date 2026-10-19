-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_inter_add_boundary_sdiff_le
-- name    : SoficGroups.KunResidualExpanderDecomposition.boundary_inter_add_boundary_sdiff_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/81ec3691-6a84-4a5d-9306-241b55f068c1
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.boundary_inter_add_boundary_sdiff_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.KunResidualExpanderDecomposition.boundary_inter_add_boundary_sdiff_le {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (R U : Finset V) :
    SoficGroups.boundary σ (R ∩ U) +
        SoficGroups.boundary σ (R \ U) ≤
      SoficGroups.boundary σ R + 2 * SoficGroups.boundary σ U := by sorry
