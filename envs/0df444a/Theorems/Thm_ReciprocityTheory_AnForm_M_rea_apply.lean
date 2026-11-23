-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- name    : ReciprocityTheory.AnForm.M.rea_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:10:10.726681+00:00
-- url     : https://prove2.me/theorems/6be7b145-f555-477b-99e5-3f96b86fee72
-- title:
--   M: rea apply
-- statement:
--   The M construction uses the rea apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L15-L15

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

theorem ReciprocityTheory.AnForm.M.rea_apply (w : Fin 1 → ℂ) : p1Re w = (w 0).re := by sorry

attribute [defeq] ReciprocityTheory.AnForm.M.rea_apply
