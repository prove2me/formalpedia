-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedComponentMidrankVariation_sum_partition_parts_eq
-- name    : SoficGroups.KunCompletedComponentMidrankVariation.sum_partition_parts_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/9b586c1f-0af2-4890-b5d0-b24f83c2c35f
-- title:
--   SoficGroups.KunCompletedComponentMidrankVariation.sum_partition_parts_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedComponentMidrankVariation
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunCompletedComponentMidrankVariation.sum_partition_parts_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V)) (f : V → ℝ) :
    (∑ C ∈ P.parts, ∑ x ∈ C, f x) = ∑ x : V, f x := by sorry
