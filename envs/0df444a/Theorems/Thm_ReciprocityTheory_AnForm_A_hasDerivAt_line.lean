-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hasDerivAt_line
-- name    : ReciprocityTheory.AnForm.A.hasDerivAt_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:02.760172+00:00
-- url     : https://prove2.me/theorems/eac5447d-9627-4110-8455-bf7701b363d0
-- title:
--   A: has Deriv At line
-- statement:
--   The A construction uses the has Deriv At line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L211-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L211-L212

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ReciprocityTheory.AnForm.A.hasDerivAt_line (z w : E) (s : ℝ) : HasDerivAt (fun s : ℝ => z + s • w) w s := by sorry
