-- Prove2me | Theorems.Thm_SoficGroups_MidrankPermutationEnergy_partitionVertexMidrank_permutation_energy_tendsto_zero
-- name    : SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank_permutation_energy_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/b4cf0cb2-1389-4b1b-a17d-74503be82f9b
-- title:
--   SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank_permutation_energy_tendsto_zero
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

theorem SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank_permutation_energy_tendsto_zero
    (V ι : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    [∀ n, Fintype (ι n)]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (p : (n : ℕ) → ι n → Equiv.Perm (V n))
    (N : ℕ → ℝ)
    (hN : ∀ n, 0 < N n)
    (hcross : Tendsto
      (fun n =>
        (∑ i : ι n, ((partitionWordCrossing (P n) (p n i)).card : ℝ)) /
          N n)
      atTop (nhds 0))
    (hrank : Tendsto
      (fun n =>
        (∑ i : ι n,
          ((rankDecreasingVertices Finset.univ (b n) (p n i)).card : ℝ)) /
            N n)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ i : ι n, ∑ x : V n,
          (partitionVertexMidrank (P n) (b n) (p n i x) -
            partitionVertexMidrank (P n) (b n) x) ^ 2) / N n)
      atTop (nhds 0) := by sorry
