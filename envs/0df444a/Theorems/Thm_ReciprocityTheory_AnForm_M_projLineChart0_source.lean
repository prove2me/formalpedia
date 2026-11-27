-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_projLineChart0_source
-- name    : ReciprocityTheory.AnForm.M.projLineChart0_source
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:21.483293+00:00
-- url     : https://prove2.me/theorems/db69c3f3-10a2-4e0f-8bb7-5f12f61c4742
-- title:
--   M: proj Line Chart0 source
-- statement:
--   The M construction uses the proj Line Chart0 source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L95-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L95-L95

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.M.projLineChart0_source : projectiveLineChartAtZero.source = Set.range ((↑) : ℂ → OnePoint ℂ) := by sorry
