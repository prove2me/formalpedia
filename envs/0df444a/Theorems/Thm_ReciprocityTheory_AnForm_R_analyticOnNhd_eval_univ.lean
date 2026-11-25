-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_analyticOnNhd_eval_univ
-- name    : ReciprocityTheory.AnForm.R.analyticOnNhd_eval_univ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:10.601806+00:00
-- url     : https://prove2.me/theorems/19d7c548-d037-5372-b5b3-c98aef35444a
-- title:
--   R: analytic On Nhd eval univ
-- statement:
--   The R construction uses the analytic On Nhd eval univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L166-L168

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.R.analyticOnNhd_eval_univ (q : MvPolynomial (Fin n) ℂ) :
    AnalyticOnNhd ℂ (fun y : Fin n → ℂ => eval y q) Set.univ := by sorry
