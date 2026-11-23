-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_hasDerivAt_fubiniStudyProfileInv
-- name    : ReciprocityTheory.AnForm.M.hasDerivAt_fubiniStudyProfileInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:36.325624+00:00
-- url     : https://prove2.me/theorems/49ea0414-6c4d-4913-8fae-c521314ee5e2
-- title:
--   M: has Deriv At fubini Study Profile Inv
-- statement:
--   The M construction uses the has Deriv At fubini Study Profile Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L169-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L169-L177

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

theorem ReciprocityTheory.AnForm.M.hasDerivAt_fubiniStudyProfileInv {t : ℝ} (ht : 0 < t) :
    HasDerivAt fubiniStudyProfileInv (-(1 / 2) * (t * (t + 1))⁻¹) t := by sorry
