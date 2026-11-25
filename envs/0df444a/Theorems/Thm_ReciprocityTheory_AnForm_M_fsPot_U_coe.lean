-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_coe
-- name    : ReciprocityTheory.AnForm.M.fsPot_U_coe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:09.333107+00:00
-- url     : https://prove2.me/theorems/3e202934-c62a-4508-96b3-132a0f85e404
-- title:
--   M: fs Pot U coe
-- statement:
--   The M construction uses the fs Pot U coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L190-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L190-L190

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

theorem ReciprocityTheory.AnForm.M.fsPot_U_coe (z : ℂ) : fsPot.U (z : OnePoint ℂ) = projectiveLineChartAtZero.source := by sorry
