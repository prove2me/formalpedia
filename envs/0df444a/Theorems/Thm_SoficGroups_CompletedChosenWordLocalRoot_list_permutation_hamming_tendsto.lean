-- Prove2me | Theorems.Thm_SoficGroups_CompletedChosenWordLocalRoot_list_permutation_hamming_tendsto
-- name    : SoficGroups.CompletedChosenWordLocalRoot.list_permutation_hamming_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/1dc4153c-7b9c-4a81-9247-8d5beb89b7ba
-- title:
--   SoficGroups.CompletedChosenWordLocalRoot.list_permutation_hamming_tendsto
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedChosenWordLocalRoot
open Filter Topology
open scoped BigOperators

theorem SoficGroups.CompletedChosenWordLocalRoot.list_permutation_hamming_tendsto
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {ι : Type*}
    (σ τ : ∀ n, ι → Equiv.Perm (V n))
    (hletter : ∀ i : ι,
      Tendsto
        (fun n => SoficGroups.normalizedHamming (σ n i) (τ n i))
        atTop (nhds 0))
    (l : List ι) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        ((l.map (σ n)).prod) ((l.map (τ n)).prod))
      atTop (nhds 0) := by sorry
