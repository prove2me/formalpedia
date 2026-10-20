-- Prove2me | Theorems.Thm_SoficGroups_almostCentralizerCluster_eq_iff
-- name    : SoficGroups.almostCentralizerCluster_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/1f208031-56dc-4953-9ff6-d85010179b40
-- title:
--   SoficGroups.almostCentralizerCluster_eq_iff
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

theorem SoficGroups.almostCentralizerCluster_eq_iff {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (p q : AlmostCentralizerElement σ tolerance) :
    almostCentralizerCluster hgap p = almostCentralizerCluster hgap q ↔
      5 * permutationDistance p.permutation q.permutation ≤ Fintype.card V := by sorry
