-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_log_sum_nonneg
-- name    : ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:24.412799+00:00
-- url     : https://prove2.me/theorems/f6cd3021-1fdf-4236-a915-c46340c89b33
-- title:
--   L2 Dbar Estimates: levi V log sum nonneg
-- statement:
--   The L2 Dbar Estimates construction uses the levi V log sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L190-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L190-L213

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg {m : ℕ} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, ContDiffAt ℝ 2 (u i) x) (hl : ∀ i, LogPshAt n (u i) x) (hpos : 0 < ∑ i, u i x)
    (ξ : Fin n → ℂ) : 0 ≤ (leviV n (fun y => ((Real.log (∑ i, u i y) : ℝ) : ℂ)) x ξ).re := by sorry
