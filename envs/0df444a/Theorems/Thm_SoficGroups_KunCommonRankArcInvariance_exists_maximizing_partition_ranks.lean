-- Prove2me | Theorems.Thm_SoficGroups_KunCommonRankArcInvariance_exists_maximizing_partition_ranks
-- name    : SoficGroups.KunCommonRankArcInvariance.exists_maximizing_partition_ranks
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/8be9feee-56e0-420a-a2e7-4215f8a9114a
-- title:
--   SoficGroups.KunCommonRankArcInvariance.exists_maximizing_partition_ranks
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

theorem SoficGroups.KunCommonRankArcInvariance.exists_maximizing_partition_ranks
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ) :
    ∃ j : (n : ℕ) → Finset (V n) → ℤ,
      ∀ n C, C ∈ (P n).parts →
        j n C ∈ C.image (b n) ∧
          ∀ k ∈ C.image (b n),
            SoficGroups.componentRankMass C (b n) k ≤
              SoficGroups.componentRankMass C (b n) (j n C) := by sorry
