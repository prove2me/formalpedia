-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_dNormSq_apply
-- name    : ReciprocityTheory.AnForm.M.dNormSq_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:16.945966+00:00
-- url     : https://prove2.me/theorems/507816b4-cfb9-4af1-8716-388218e608c1
-- title:
--   M: d Norm Sq apply
-- statement:
--   The M construction uses the d Norm Sq apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L21-L24

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

theorem ReciprocityTheory.AnForm.M.dNormSq_apply (w v : Fin 1 → ℂ) :
    projectiveLineNormSqDerivative w v = 2 * ((w 0).re * (v 0).re + (w 0).im * (v 0).im) := by sorry
