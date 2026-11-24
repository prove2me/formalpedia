-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_poissonKernel_zero_continuousOn
-- name    : ReciprocityTheory.AnForm.A.poissonKernel_zero_continuousOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:10.062825+00:00
-- url     : https://prove2.me/theorems/1aaef268-f1dd-4d0e-bf46-1aa66d20eaaf
-- title:
--   A: poisson Kernel zero continuous On
-- statement:
--   The A construction uses the poisson Kernel zero continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L28-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric Real Filter Topology InnerProductSpace
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

theorem ReciprocityTheory.AnForm.A.poissonKernel_zero_continuousOn {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    ContinuousOn (poissonKernel 0 w) (sphere 0 r) := by sorry
