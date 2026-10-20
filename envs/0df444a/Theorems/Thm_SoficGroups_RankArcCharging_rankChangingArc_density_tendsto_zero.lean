-- Prove2me | Theorems.Thm_SoficGroups_RankArcCharging_rankChangingArc_density_tendsto_zero
-- name    : SoficGroups.RankArcCharging.rankChangingArc_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/c20d8d1e-fff7-4aea-a290-104cf5842bbd
-- title:
--   SoficGroups.RankArcCharging.rankChangingArc_density_tendsto_zero
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
open SoficGroups.RankArcCharging
open scoped BigOperators

theorem SoficGroups.RankArcCharging.rankChangingArc_density_tendsto_zero
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n))
    (P : ∀ n, Finpartition (U n))
    (b : ∀ n, V n → ℤ)
    (j : ∀ n, Finset (V n) → ℤ)
    (w : ∀ n, Equiv.Perm (V n))
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (hcross : Filter.Tendsto
      (fun n => ((partitionWordCrossing (P n) (w n)).card : ℝ) / N n)
      Filter.atTop (nhds 0))
    (homit : Filter.Tendsto
      (fun n =>
        (((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) /
          N n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ((rankChangingArc (U n) (b n) (w n)).card : ℝ) / N n)
      Filter.atTop (nhds 0) := by sorry
