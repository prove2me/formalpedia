-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionRetainedDiscard_retained_missing_density_tendsto_zero
-- name    : SoficGroups.SourceCompressionRetainedDiscard.retained_missing_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/90155d63-bcb8-44ac-9ad9-c9435915e972
-- title:
--   SoficGroups.SourceCompressionRetainedDiscard.retained_missing_density_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionRetainedDiscard
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.SourceCompressionRetainedDiscard.retained_missing_density_tendsto_zero
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (P Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (V n)))
    (T : (n : ℕ) → Equiv.Perm (V n))
    (b : (n : ℕ) → V n → ℤ) (eta : ℕ → ℝ)
    (heta : Tendsto eta atTop (nhds 0))
    (hoverlap : Tendsto
      (fun n =>
        ((∑ C ∈ SoficGroups.insufficientOverlapComponents
          (P n) (Q n) (eta n), C.card : ℕ) : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hrank : Tendsto
      (fun n =>
        ((SoficGroups.RankArcCharging.rankChangingArc
          (Finset.univ : Finset (V n)) (b n) (T n).symm).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (((Finset.univ : Finset (V n)) \
          SoficGroups.matchedRetainedSupport
            (retainedComponents (P n) (Q n) (T n) (b n)
              (eta n))).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0) := by sorry
