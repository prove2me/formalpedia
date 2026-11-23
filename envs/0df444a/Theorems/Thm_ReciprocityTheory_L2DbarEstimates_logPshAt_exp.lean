-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_logPshAt_exp
-- name    : ReciprocityTheory.L2DbarEstimates.logPshAt_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:00.941403+00:00
-- url     : https://prove2.me/theorems/ef273fb2-ac8e-496c-addf-06c0748fcd68
-- title:
--   L2 Dbar Estimates: log Psh At exp
-- statement:
--   The L2 Dbar Estimates construction uses the log Psh At exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L117-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L117-L140

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

theorem ReciprocityTheory.L2DbarEstimates.logPshAt_exp {φ : V n → ℝ} {x : V n} (hφ : ContDiffAt ℝ 2 φ x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun y => (φ y : ℂ)) x ξ).re) :
    LogPshAt n (fun y => Real.exp (φ y)) x := by sorry
