-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_chart_chartIndexAt_infty
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.chart_chartIndexAt_infty
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:28:27.052373+00:00
-- url     : https://prove2.me/theorems/91d6ac6f-7d24-4db5-8586-4d38f86f84b6
-- title:
--   Compatible Chart Operations: chart chart Index At infty
-- statement:
--   The Compatible Chart Operations construction uses the chart chart Index At infty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L160-L162

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

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.chart_chartIndexAt_infty {a : OnePoint ℂ} (ha : a = ∞) : p1.chart (chartIndexAt a) = projectiveLineChartAtInfinity := by sorry
