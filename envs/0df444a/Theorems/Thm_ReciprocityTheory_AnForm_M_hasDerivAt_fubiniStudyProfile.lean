-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_hasDerivAt_fubiniStudyProfile
-- name    : ReciprocityTheory.AnForm.M.hasDerivAt_fubiniStudyProfile
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:37.141663+00:00
-- url     : https://prove2.me/theorems/039db0c3-50f8-401f-b75c-8013b14b8d4b
-- title:
--   M: has Deriv At fubini Study Profile
-- statement:
--   The M construction uses the has Deriv At fubini Study Profile property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L164-L167

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

theorem ReciprocityTheory.AnForm.M.hasDerivAt_fubiniStudyProfile {t : ℝ} (ht : -1 < t) : HasDerivAt fubiniStudyProfile ((1 / 2) * (1 + t)⁻¹) t := by sorry
