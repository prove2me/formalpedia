-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
-- name    : ReciprocityTheory.L2DbarEstimates.LogPshAt.congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:48.759059+00:00
-- url     : https://prove2.me/theorems/616c469d-34dc-4c4d-a109-5100d02ae820
-- title:
--   Log Psh At: congr
-- statement:
--   The Log Psh At construction uses the congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L108-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/OfRealNormSqSumMul.lean#L108-L115

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

theorem ReciprocityTheory.L2DbarEstimates.LogPshAt.congr {u w : V n → ℝ} {x : V n} (h : u =ᶠ[𝓝 x] w) (hu : LogPshAt n u x) :
    LogPshAt n w x := by sorry
