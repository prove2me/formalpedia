-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionMatching_symmDiff_density_tendsto_zero_of_log_rank_bounds
-- name    : SoficGroups.SourceCompressionMatching.symmDiff_density_tendsto_zero_of_log_rank_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/1ac4a38b-a8f1-4534-8854-cbe23b3103e2
-- title:
--   SoficGroups.SourceCompressionMatching.symmDiff_density_tendsto_zero_of_log_rank_bounds
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.SourceCompressionMatching.symmDiff_density_tendsto_zero_of_log_rank_bounds
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (H eta : ℕ → ℝ)
    (hH : ∀ n, 0 ≤ H n) (heta : ∀ n, 0 ≤ eta n)
    (hHzero : Tendsto H atTop (nhds 0))
    (hetazero : Tendsto eta atTop (nhds 0))
    (hbound : ∀ n C, C ∈ R n →
      ((C ∆ D n C).card : ℝ) ≤
        (Real.exp (H n) - 1 + 2 * eta n) * (C.card : ℝ)) :
    Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (nhds 0) := by sorry
