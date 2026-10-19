-- Prove2me | Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_generator_crossing_density_tendsto_zero
-- name    : SoficGroups.SourceGeneratedWordCrossing.generator_crossing_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/f98f9ff3-0680-4821-90c2-33991e3f4826
-- title:
--   SoficGroups.SourceGeneratedWordCrossing.generator_crossing_density_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceGeneratedWordCrossing.generator_crossing_density_tendsto_zero
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : ∀ n, ι → Equiv.Perm (V n))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (i : ι) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          (σ n i)).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0) := by sorry
