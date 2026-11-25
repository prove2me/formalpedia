-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_chartIdeal_le_ptIdealOf
-- name    : ReciprocityTheory.AnForm.R.chartIdeal_le_ptIdealOf
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:17:23.746045+00:00
-- url     : https://prove2.me/theorems/be944b84-1940-4872-b10a-5083d8855455
-- title:
--   R: chart Ideal le pt Ideal Of
-- statement:
--   The R construction uses the chart Ideal le pt Ideal Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChart.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChart.lean#L12-L16

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.chartIdeal_le_ptIdealOf {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {p : (k : K) → ι k}
    {z : (Σ k, ι k) → ℂ} (hz : ∀ h ∈ chartIdeal P p, eval z h = 0) :
    chartIdeal P p ≤ ptIdealOf z := by sorry
