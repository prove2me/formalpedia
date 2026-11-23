-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffAt_normSq_comp
-- name    : ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:17.824352+00:00
-- url     : https://prove2.me/theorems/96e5364f-1ce7-483f-a909-b2516c923f5a
-- title:
--   L2 Dbar Estimates: cont Diff At norm Sq comp
-- statement:
--   The L2 Dbar Estimates construction uses the cont Diff At norm Sq comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LogNormSq.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LogNormSq.lean#L19-L25

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    ContDiffAt ℝ 2 (fun y => Complex.normSq (g y)) x := by sorry
