-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_le_degree_mul_card
-- name    : SoficGroups.KunResidualExpanderDecomposition.boundary_le_degree_mul_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/25056f91-1d5f-4403-a14f-60dbbd7c3bde
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.boundary_le_degree_mul_card
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

theorem SoficGroups.KunResidualExpanderDecomposition.boundary_le_degree_mul_card {V ι : Type*}
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) :
    SoficGroups.boundary σ A ≤ Fintype.card ι * A.card := by sorry
