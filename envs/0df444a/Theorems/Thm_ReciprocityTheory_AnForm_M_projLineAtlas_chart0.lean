-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_projLineAtlas_chart0
-- name    : ReciprocityTheory.AnForm.M.projLineAtlas_chart0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:47.994055+00:00
-- url     : https://prove2.me/theorems/882977b8-8a73-4763-b603-a77d3642de1d
-- title:
--   M: proj Line Atlas chart0
-- statement:
--   The M construction uses the proj Line Atlas chart0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L168-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L168-L168

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

theorem ReciprocityTheory.AnForm.M.projLineAtlas_chart0 : p1.chart (0 : Fin 2) = projectiveLineChartAtZero := by sorry
