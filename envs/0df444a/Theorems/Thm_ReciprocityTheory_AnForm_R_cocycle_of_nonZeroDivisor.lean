-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_cocycle_of_nonZeroDivisor
-- name    : ReciprocityTheory.AnForm.R.cocycle_of_nonZeroDivisor
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:43:14.925347+00:00
-- url     : https://prove2.me/theorems/715ab916-a4df-46ec-80b2-831f7fbd1490
-- title:
--   R: cocycle of non Zero Divisor
-- statement:
--   The R construction uses the cocycle of non Zero Divisor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WCharts.lean#L86-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WCharts.lean#L86-L95

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section

theorem ReciprocityTheory.AnForm.R.cocycle_of_nonZeroDivisor {Ri Rj O : Type*} [CommRing Ri] [CommRing Rj] [CommRing O]
    (ri : Ri →+* O) (rj : Rj →+* O) {Gi Gj Gk tij tik : Ri} {Gj' Gk' tjk : Rj} {Oj Ok : O}
    (h1 : Gj = tij * Gi) (h2 : Gk = tik * Gi) (h3 : Gk' = tjk * Gj')
    (e1 : ri Gj = Oj) (e2 : rj Gj' = Oj) (e3 : ri Gk = Ok) (e4 : rj Gk' = Ok)
    (hG : ri Gi ∈ nonZeroDivisors O) : rj tjk * ri tij = ri tik := by sorry
