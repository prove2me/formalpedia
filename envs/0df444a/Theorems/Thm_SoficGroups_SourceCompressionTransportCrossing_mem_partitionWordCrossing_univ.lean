-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_mem_partitionWordCrossing_univ
-- name    : SoficGroups.SourceCompressionTransportCrossing.mem_partitionWordCrossing_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/4b362e96-e87a-4cdb-b0e0-faaf6da41348
-- title:
--   SoficGroups.SourceCompressionTransportCrossing.mem_partitionWordCrossing_univ
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

theorem SoficGroups.SourceCompressionTransportCrossing.mem_partitionWordCrossing_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : Equiv.Perm V) (x : V) :
    x ∈ SoficGroups.partitionWordCrossing Q p ↔
      Q.part x ≠ Q.part (p x) := by sorry
