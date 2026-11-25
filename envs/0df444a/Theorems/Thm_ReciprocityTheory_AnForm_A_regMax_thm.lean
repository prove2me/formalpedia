-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_thm
-- name    : ReciprocityTheory.AnForm.A.regMax_thm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:18.024357+00:00
-- url     : https://prove2.me/theorems/a402f1a8-f54f-4bfa-acd9-f129c37a8316
-- title:
--   A: reg Max thm
-- statement:
--   The A construction uses the reg Max thm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L139-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L139-L148

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

theorem ReciprocityTheory.AnForm.A.regMax_thm : RegMaxStatement := by sorry
