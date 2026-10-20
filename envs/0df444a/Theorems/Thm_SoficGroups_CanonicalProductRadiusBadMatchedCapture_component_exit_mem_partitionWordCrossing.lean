-- Prove2me | Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_component_exit_mem_partitionWordCrossing
-- name    : SoficGroups.CanonicalProductRadiusBadMatchedCapture.component_exit_mem_partitionWordCrossing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/d592c65d-870e-474e-9fa3-e62bc66f5850
-- title:
--   SoficGroups.CanonicalProductRadiusBadMatchedCapture.component_exit_mem_partitionWordCrossing
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.ChosenCayleyMatchedComponentRealization
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open scoped BigOperators Pointwise symmDiff

theorem SoficGroups.CanonicalProductRadiusBadMatchedCapture.component_exit_mem_partitionWordCrossing
    {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U)
    (C : Finset V) (hC : C ∈ P.parts)
    (p : Equiv.Perm V) {x : V}
    (hx : x ∈ C) (hout : p x ∉ C) :
    x ∈ SoficGroups.partitionWordCrossing P p := by sorry
