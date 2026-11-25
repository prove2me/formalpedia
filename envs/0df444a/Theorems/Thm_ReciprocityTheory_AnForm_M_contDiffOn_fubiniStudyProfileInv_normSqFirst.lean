-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_contDiffOn_fubiniStudyProfileInv_normSqFirst
-- name    : ReciprocityTheory.AnForm.M.contDiffOn_fubiniStudyProfileInv_normSqFirst
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:14.90842+00:00
-- url     : https://prove2.me/theorems/d813ed3c-fe52-528d-84b8-91764b4f4a48
-- title:
--   M: cont Diff On fubini Study Profile Inv norm Sq First
-- statement:
--   The M construction uses the cont Diff On fubini Study Profile Inv norm Sq First property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L135-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L135-L145

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

theorem ReciprocityTheory.AnForm.M.contDiffOn_fubiniStudyProfileInv_normSqFirst : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => fubiniStudyProfileInv (fsQ w)) {w | w 0 ≠ 0} := by sorry
