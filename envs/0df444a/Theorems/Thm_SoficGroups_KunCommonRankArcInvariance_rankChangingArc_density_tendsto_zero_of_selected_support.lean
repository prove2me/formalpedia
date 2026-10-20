-- Prove2me | Theorems.Thm_SoficGroups_KunCommonRankArcInvariance_rankChangingArc_density_tendsto_zero_of_selected_support
-- name    : SoficGroups.KunCommonRankArcInvariance.rankChangingArc_density_tendsto_zero_of_selected_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/7d58f488-8f87-4565-ad2e-ef0a0985fca3
-- title:
--   SoficGroups.KunCommonRankArcInvariance.rankChangingArc_density_tendsto_zero_of_selected_support
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

theorem SoficGroups.KunCommonRankArcInvariance.rankChangingArc_density_tendsto_zero_of_selected_support
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    {κ : Type*}
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ)
    (j : (n : ℕ) → Finset (V n) → ℤ)
    (w : (n : ℕ) → κ → Equiv.Perm (V n))
    (homitted : Tendsto
      (fun n =>
        ((((Finset.univ : Finset (V n)) \
          SoficGroups.RankArcCharging.selectedRankSupport
            (P n) (b n) (j n)).card : ℝ) /
              Fintype.card (V n)))
      atTop (nhds 0))
    (hcross : ∀ i : κ, Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing
          (P n) (w n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    ∀ i : κ, Tendsto
      (fun n =>
        ((SoficGroups.RankArcCharging.rankChangingArc
          (Finset.univ : Finset (V n))
          (b n) (w n i)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by sorry
