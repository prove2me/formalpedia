-- Prove2me | Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_crossing_density_tendsto_zero_of_normalizedHamming
-- name    : SoficGroups.SourceGeneratedWordCrossing.crossing_density_tendsto_zero_of_normalizedHamming
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/c91b2792-9645-4811-8646-2ffae0b3df62
-- title:
--   SoficGroups.SourceGeneratedWordCrossing.crossing_density_tendsto_zero_of_normalizedHamming
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

theorem SoficGroups.SourceGeneratedWordCrossing.crossing_density_tendsto_zero_of_normalizedHamming
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (p q : ∀ n, Equiv.Perm (V n))
    (hq : Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n) (q n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0))
    (hdist : Tendsto
      (fun n => SoficGroups.normalizedHamming (p n) (q n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n) (p n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0) := by sorry
