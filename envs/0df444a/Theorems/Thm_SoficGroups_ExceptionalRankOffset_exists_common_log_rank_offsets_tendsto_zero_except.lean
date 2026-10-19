-- Prove2me | Theorems.Thm_SoficGroups_ExceptionalRankOffset_exists_common_log_rank_offsets_tendsto_zero_except
-- name    : SoficGroups.ExceptionalRankOffset.exists_common_log_rank_offsets_tendsto_zero_except
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/9eff0ed8-9e2a-4791-9bcb-24d08d51a5c3
-- title:
--   SoficGroups.ExceptionalRankOffset.exists_common_log_rank_offsets_tendsto_zero_except
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
open SoficGroups.ExceptionalRankOffset
open Filter Topology
open scoped BigOperators

theorem SoficGroups.ExceptionalRankOffset.exists_common_log_rank_offsets_tendsto_zero_except
    (ι : ℕ → Type*)
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (G : (n : ℕ) → Finset (ι n))
    (x y : (n : ℕ) → ι n → ℝ)
    (eta H N : ℕ → ℝ) (C : ℝ)
    (hx : ∀ n i, i ∈ G n → 0 < x n i)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (hN : ∀ n, 0 < N n)
    (hcard : ∀ n, ((G n).card : ℝ) ≤ C * N n)
    (hcomparison : ∀ n i, i ∈ G n →
      (1 - eta n) * x n i ≤ y n i)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (nhds 0))
    (hexceptions : Tendsto
      (fun n =>
        (((Finset.univ : Finset (ι n)) \ G n).card : ℝ) / N n)
      atTop (nhds 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
        Tendsto
          (fun n =>
            SoficGroups.rankDropCount
              (fun i => Real.log (x n i))
              (fun i => Real.log (y n i)) (H n) (r n) / N n)
          atTop (nhds 0) := by sorry
