-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_convex_comb
-- name    : ReciprocityTheory.AnForm.A.tmax_convex_comb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:29.596155+00:00
-- url     : https://prove2.me/theorems/89dfc3dc-10bc-4566-8c50-081058e1a1b0
-- title:
--   A: tmax convex comb
-- statement:
--   The A construction uses the tmax convex comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L64-L68

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem ReciprocityTheory.AnForm.A.tmax_convex_comb (x y : ι → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    tmax (a • x + b • y) ≤ a * tmax x + b * tmax y := by sorry
