-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isPlurisubharmonic
-- name    : ReciprocityTheory.AnForm.M.projLine_isPlurisubharmonic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:24.031887+00:00
-- url     : https://prove2.me/theorems/307afa69-18a5-52e0-bc04-9274489c1c7d
-- title:
--   M: proj Line is Plurisubharmonic
-- statement:
--   The M construction uses the proj Line is Plurisubharmonic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L377-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L377-L416

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

theorem ReciprocityTheory.AnForm.M.projLine_isPlurisubharmonic : IsPsh p1 fsPot := by sorry
