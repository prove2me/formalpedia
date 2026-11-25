-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_contDiff_fubiniStudyProfile_normSqFirst
-- name    : ReciprocityTheory.AnForm.M.contDiff_fubiniStudyProfile_normSqFirst
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:36.535797+00:00
-- url     : https://prove2.me/theorems/266f843f-ce37-422c-bb05-b886a833d2e6
-- title:
--   M: cont Diff fubini Study Profile norm Sq First
-- statement:
--   The M construction uses the cont Diff fubini Study Profile norm Sq First property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L129-L133

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
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

theorem ReciprocityTheory.AnForm.M.contDiff_fubiniStudyProfile_normSqFirst : ContDiff ℝ (⊤ : ℕ∞) (fun w => fubiniStudyProfile (fsQ w)) := by sorry
