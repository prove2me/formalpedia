-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_analyticAt_inv_apply_zero
-- name    : ReciprocityTheory.AnForm.M.projLine_analyticAt_inv_apply_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:25.407206+00:00
-- url     : https://prove2.me/theorems/9c69d754-2739-4eee-8bf5-ac887d516e6a
-- title:
--   M: proj Line analytic At inv apply zero
-- statement:
--   The M construction uses the proj Line analytic At inv apply zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffOnFubiniStudyProfileInvNormSqFirst.lean#L114-L115

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

theorem ReciprocityTheory.AnForm.M.projLine_analyticAt_inv_apply_zero {w : Fin 1 → ℂ} (hw : w 0 ≠ 0) :
    AnalyticAt ℂ (fun w : Fin 1 → ℂ => (w 0)⁻¹) w := by sorry
