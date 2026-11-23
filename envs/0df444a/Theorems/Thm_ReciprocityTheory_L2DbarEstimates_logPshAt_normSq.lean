-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_logPshAt_normSq
-- name    : ReciprocityTheory.L2DbarEstimates.logPshAt_normSq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:42.460494+00:00
-- url     : https://prove2.me/theorems/5256d1f8-78ca-4eb7-b03f-af0094bc4e1e
-- title:
--   L2 Dbar Estimates: log Psh At norm Sq
-- statement:
--   The L2 Dbar Estimates construction uses the log Psh At norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L142-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L142-L185

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

theorem ReciprocityTheory.L2DbarEstimates.logPshAt_normSq {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    LogPshAt n (fun y => Complex.normSq (g y)) x := by sorry
