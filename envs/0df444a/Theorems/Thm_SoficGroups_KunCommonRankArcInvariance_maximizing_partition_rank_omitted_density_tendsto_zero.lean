-- Prove2me | Theorems.Thm_SoficGroups_KunCommonRankArcInvariance_maximizing_partition_rank_omitted_density_tendsto_zero
-- name    : SoficGroups.KunCommonRankArcInvariance.maximizing_partition_rank_omitted_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/60f8948d-12e0-4015-9fa6-932cd37f45a1
-- title:
--   SoficGroups.KunCommonRankArcInvariance.maximizing_partition_rank_omitted_density_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCommonRankArcInvariance
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunCommonRankArcInvariance.maximizing_partition_rank_omitted_density_tendsto_zero
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (j : (n : ℕ) → Finset (V n) → ℤ)
    (hmax : ∀ n C, C ∈ (P n).parts →
      ∀ k ∈ C.image (b n),
        SoficGroups.componentRankMass C (b n) k ≤
          SoficGroups.componentRankMass C (b n) (j n C))
    (hvariance : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C (b n))) /
                Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((((Finset.univ : Finset (V n)) \
          SoficGroups.RankArcCharging.selectedRankSupport
            (P n) (b n) (j n)).card : ℝ) /
              Fintype.card (V n)))
      atTop (nhds 0) := by sorry
