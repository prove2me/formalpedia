-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_circleAverage_poissonKernel_zero
-- name    : ReciprocityTheory.AnForm.A.circleAverage_poissonKernel_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:57.359798+00:00
-- url     : https://prove2.me/theorems/84fa8253-1db1-4f1e-8330-aaf09982ccfd
-- title:
--   A: circle Average poisson Kernel zero
-- statement:
--   The A construction uses the circle Average poisson Kernel zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L65-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L65-L126

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

theorem ReciprocityTheory.AnForm.A.circleAverage_poissonKernel_zero {r : ℝ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    Real.circleAverage (poissonKernel 0 w) 0 r = 1 := by sorry
