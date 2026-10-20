-- Prove2me | Theorems.Thm_SoficGroups_MidrankPermutationEnergy_midpointDecreasing_subset_crossing_union_rankDecreasing
-- name    : SoficGroups.MidrankPermutationEnergy.midpointDecreasing_subset_crossing_union_rankDecreasing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/21764a76-e644-4ce9-9969-dbc0bb033360
-- title:
--   SoficGroups.MidrankPermutationEnergy.midpointDecreasing_subset_crossing_union_rankDecreasing
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
open SoficGroups.MidrankPermutationEnergy

theorem SoficGroups.MidrankPermutationEnergy.midpointDecreasing_subset_crossing_union_rankDecreasing
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (p : Equiv.Perm V) :
    midpointDecreasingVertices P b p ⊆
      partitionWordCrossing P p ∪ rankDecreasingVertices U b p := by sorry
