-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isSmoothPotential
-- name    : ReciprocityTheory.AnForm.M.projLine_isSmoothPotential
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:50.500942+00:00
-- url     : https://prove2.me/theorems/67ae9db5-36a5-48f7-b04b-c98a9822e1c7
-- title:
--   M: proj Line is Smooth Potential
-- statement:
--   The M construction uses the proj Line is Smooth Potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L337-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L337-L375

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

theorem ReciprocityTheory.AnForm.M.projLine_isSmoothPotential : IsPotential p1 fsPot := by sorry
