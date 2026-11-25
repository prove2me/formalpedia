-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_poissonKernel_zero_le
-- name    : ReciprocityTheory.AnForm.A.poissonKernel_zero_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:32.559534+00:00
-- url     : https://prove2.me/theorems/353b7075-d464-4656-bcbf-d1d5d1b5bbba
-- title:
--   A: poisson Kernel zero le
-- statement:
--   The A construction uses the poisson Kernel zero le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L50-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshPoisson.lean#L50-L63

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

theorem ReciprocityTheory.AnForm.A.poissonKernel_zero_le {r δ : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) (hδ : 0 < δ) (hzw : δ ≤ ‖z - w‖) :
    poissonKernel 0 w z ≤ (r ^ 2 - ‖w‖ ^ 2) / δ ^ 2 := by sorry
