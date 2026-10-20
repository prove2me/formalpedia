-- Prove2me | Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_sum_intersection_boundary_le_partition_boundaries
-- name    : SoficGroups.KunTransportedAmbientOverlap.sum_intersection_boundary_le_partition_boundaries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/4829a84a-55be-4fa7-a979-3a499c9ad302
-- title:
--   SoficGroups.KunTransportedAmbientOverlap.sum_intersection_boundary_le_partition_boundaries
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.KunTransportedAmbientOverlap.sum_intersection_boundary_le_partition_boundaries
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    {U : Finset V} (P Q : Finpartition U)
    (σ : ι → Equiv.Perm V) :
    (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
      SoficGroups.boundary σ (C ∩ D)) ≤
      (∑ C ∈ P.parts, SoficGroups.boundary σ C) +
        (∑ D ∈ Q.parts, SoficGroups.boundary σ D) := by sorry
