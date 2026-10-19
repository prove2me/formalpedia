-- Prove2me | Theorems.Thm_SoficGroups_MidrankPermutationEnergy_sum_partitionVertexMidrank_permutation_energy_le
-- name    : SoficGroups.MidrankPermutationEnergy.sum_partitionVertexMidrank_permutation_energy_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/a0cc2ad9-5f44-46ea-afa5-615abb487aeb
-- title:
--   SoficGroups.MidrankPermutationEnergy.sum_partitionVertexMidrank_permutation_energy_le
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

theorem SoficGroups.MidrankPermutationEnergy.sum_partitionVertexMidrank_permutation_energy_le
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (I : Finset ι)
    (P : Finpartition (Finset.univ : Finset V))
    (b : V → ℤ) (p : ι → Equiv.Perm V) :
    (∑ i ∈ I, ∑ x : V,
      (partitionVertexMidrank P b (p i x) -
        partitionVertexMidrank P b x) ^ 2) ≤
      2 * (∑ i ∈ I, ((partitionWordCrossing P (p i)).card : ℝ)) +
        2 * (∑ i ∈ I,
          ((rankDecreasingVertices Finset.univ b (p i)).card : ℝ)) := by sorry
