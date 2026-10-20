-- Prove2me | Theorems.Thm_SoficGroups_SourceCommonOffsetMidrankEnergy_exists_common_component_log_rank_with_vanishing_drops
-- name    : SoficGroups.SourceCommonOffsetMidrankEnergy.exists_common_component_log_rank_with_vanishing_drops
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/8909f99d-cc7b-4ef9-b588-74bbb521c3ec
-- title:
--   SoficGroups.SourceCommonOffsetMidrankEnergy.exists_common_component_log_rank_with_vanishing_drops
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonOffsetMidrankEnergy
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceCommonOffsetMidrankEnergy.exists_common_component_log_rank_with_vanishing_drops
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (Q : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (p : (n : ℕ) → ι → Equiv.Perm (V n))
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (nhds 0))
    (hbad : Tendsto
      (fun n =>
        ((componentSizeComparisonBad (Q n) (p n) (eta n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      Tendsto
        (fun n =>
          (∑ i : ι,
            ((SoficGroups.MidrankPermutationEnergy.rankDecreasingVertices
              Finset.univ
              (componentLogRank (Q n) (H n) (r n))
              (p n i)).card : ℝ)) /
            Fintype.card (V n))
        atTop (nhds 0) := by sorry
