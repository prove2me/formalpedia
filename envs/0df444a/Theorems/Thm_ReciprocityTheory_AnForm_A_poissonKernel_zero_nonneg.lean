-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_poissonKernel_zero_nonneg
-- name    : ReciprocityTheory.AnForm.A.poissonKernel_zero_nonneg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:27.131457+00:00
-- url     : https://prove2.me/theorems/4558b9ec-bd07-4c49-9324-aa9d38899e13
-- title:
--   A: poisson Kernel zero nonneg
-- statement:
--   The A construction uses the poisson Kernel zero nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L40-L48

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

theorem ReciprocityTheory.AnForm.A.poissonKernel_zero_nonneg {r : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) : 0 ≤ poissonKernel 0 w z := by sorry
