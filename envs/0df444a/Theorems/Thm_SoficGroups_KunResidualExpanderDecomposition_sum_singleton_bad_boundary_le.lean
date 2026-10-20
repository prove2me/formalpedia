-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_sum_singleton_bad_boundary_le
-- name    : SoficGroups.KunResidualExpanderDecomposition.sum_singleton_bad_boundary_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/4ce9c40d-5cb3-427e-b4be-eda228a04711
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.sum_singleton_bad_boundary_le
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

theorem SoficGroups.KunResidualExpanderDecomposition.sum_singleton_bad_boundary_le
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V) :
    (∑ C ∈ (⊥ : Finpartition B).parts,
      (SoficGroups.boundary σ C : ℝ)) ≤
        (Fintype.card ι : ℝ) * (B.card : ℝ) := by sorry
