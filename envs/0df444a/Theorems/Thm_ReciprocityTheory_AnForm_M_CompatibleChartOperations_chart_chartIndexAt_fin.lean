-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_chart_chartIndexAt_fin
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.chart_chartIndexAt_fin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:27:47.409359+00:00
-- url     : https://prove2.me/theorems/7b6a84ba-9f61-57a5-9444-566541d2a08b
-- title:
--   Compatible Chart Operations: chart chart Index At fin
-- statement:
--   The Compatible Chart Operations construction uses the chart chart Index At fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L164-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L164-L166

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.chart_chartIndexAt_fin {a : OnePoint ℂ} (ha : a ≠ ∞) : p1.chart (chartIndexAt a) = projectiveLineChartAtZero := by sorry
