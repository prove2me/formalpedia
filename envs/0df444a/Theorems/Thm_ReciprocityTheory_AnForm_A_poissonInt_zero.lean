-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_poissonInt_zero
-- name    : ReciprocityTheory.AnForm.A.poissonInt_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:23.658503+00:00
-- url     : https://prove2.me/theorems/8e71a512-ee75-5576-a875-499087afdca6
-- title:
--   A: poisson Int zero
-- statement:
--   The A construction uses the poisson Int zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L231-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L231-L240

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

theorem ReciprocityTheory.AnForm.A.poissonInt_zero {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) :
    poissonInt g r 0 = Real.circleAverage g 0 r := by sorry
