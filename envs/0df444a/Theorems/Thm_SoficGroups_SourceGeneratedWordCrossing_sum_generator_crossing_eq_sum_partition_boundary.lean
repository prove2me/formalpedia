-- Prove2me | Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_sum_generator_crossing_eq_sum_partition_boundary
-- name    : SoficGroups.SourceGeneratedWordCrossing.sum_generator_crossing_eq_sum_partition_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/bfc15f2d-2871-4901-9261-d77893dcd538
-- title:
--   SoficGroups.SourceGeneratedWordCrossing.sum_generator_crossing_eq_sum_partition_boundary
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceGeneratedWordCrossing.sum_generator_crossing_eq_sum_partition_boundary
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V) :
    (∑ i : ι, (SoficGroups.partitionWordCrossing Q (σ i)).card) =
      ∑ C ∈ Q.parts, SoficGroups.boundary σ C := by sorry
