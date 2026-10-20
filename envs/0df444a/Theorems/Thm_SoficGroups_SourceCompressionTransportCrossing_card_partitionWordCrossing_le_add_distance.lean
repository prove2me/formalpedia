-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_card_partitionWordCrossing_le_add_distance
-- name    : SoficGroups.SourceCompressionTransportCrossing.card_partitionWordCrossing_le_add_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/a72c3ba4-ce4d-41c7-a935-2efe5fd3af93
-- title:
--   SoficGroups.SourceCompressionTransportCrossing.card_partitionWordCrossing_le_add_distance
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionTransportCrossing
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceCompressionTransportCrossing.card_partitionWordCrossing_le_add_distance
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p q : Equiv.Perm V) :
    (SoficGroups.partitionWordCrossing Q p).card ≤
      (SoficGroups.partitionWordCrossing Q q).card +
        SoficGroups.permutationDistance p q := by sorry
