-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_dualEv_fst
-- name    : ReciprocityTheory.AnForm.R.dualEv_fst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:58.366139+00:00
-- url     : https://prove2.me/theorems/85ef5709-58f6-41e7-83e1-36ef2a319cb3
-- title:
--   R: dual Ev fst
-- statement:
--   The R construction uses the dual Ev fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L50-L51

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

theorem ReciprocityTheory.AnForm.R.dualEv_fst (p v : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    (dualEv p v h).fst = eval p h := by sorry
