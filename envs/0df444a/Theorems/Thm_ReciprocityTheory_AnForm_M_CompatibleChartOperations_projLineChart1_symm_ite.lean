-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_projLineChart1_symm_ite
-- name    : ReciprocityTheory.AnForm.M.CompatibleChartOperations.projLineChart1_symm_ite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:55.085277+00:00
-- url     : https://prove2.me/theorems/37828ec1-5955-46b8-a6d3-3e125ca4fa5b
-- title:
--   Compatible Chart Operations: proj Line Chart1 symm ite
-- statement:
--   The Compatible Chart Operations construction uses the proj Line Chart1 symm ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HomogeneousLiftHolomorphicOnSnd.lean#L73-L74

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations
open scoped Classical

theorem ReciprocityTheory.AnForm.M.CompatibleChartOperations.projLineChart1_symm_ite (t : Fin 1 → ℂ) :
    projectiveLineChartAtInfinity.symm t = if t 0 = 0 then ∞ else (((t 0)⁻¹ : ℂ) : OnePoint ℂ) := by sorry
