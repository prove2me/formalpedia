-- Prove2me | Theorems.Thm_SoficGroups_MidrankPermutationEnergy_rankDropCount_eq_sum_rankDecreasingVertices
-- name    : SoficGroups.MidrankPermutationEnergy.rankDropCount_eq_sum_rankDecreasingVertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/9ecf804f-cc92-4918-90e4-dd9a688fef24
-- title:
--   SoficGroups.MidrankPermutationEnergy.rankDropCount_eq_sum_rankDecreasingVertices
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

theorem SoficGroups.MidrankPermutationEnergy.rankDropCount_eq_sum_rankDecreasingVertices
    {V ι : Type*} [Fintype V] [Fintype ι]
    (u : V → ℝ) (p : ι → Equiv.Perm V) (H r : ℝ) :
    SoficGroups.rankDropCount
      (fun e : ι × V => u e.2)
      (fun e : ι × V => u (p e.1 e.2)) H r =
        ∑ i : ι,
          ((rankDecreasingVertices Finset.univ
            (offsetFloorRank u H r) (p i)).card : ℝ) := by sorry
