-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_dualEv_fst_snd
-- name    : ReciprocityTheory.AnForm.R.dualEv_fst_snd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:54.523883+00:00
-- url     : https://prove2.me/theorems/2d8505bb-7247-4e6e-930f-db53c5b6887a
-- title:
--   R: dual Ev fst snd
-- statement:
--   The R construction uses the dual Ev fst snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L16-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L16-L48

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

theorem ReciprocityTheory.AnForm.R.dualEv_fst_snd (p v : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    (dualEv p v h).fst = eval p h ∧
      (dualEv p v h).snd = ∑ j, eval p (pderiv j h) * v j := by sorry
