-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_conePts_of_chartIdeal
-- name    : ReciprocityTheory.AnForm.R.conePts_of_chartIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:27.410803+00:00
-- url     : https://prove2.me/theorems/7a1ea13c-6144-42c8-8dc3-906683b8bd6d
-- title:
--   R: cone Pts of chart Ideal
-- statement:
--   The R construction uses the cone Pts of chart Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L87-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L87-L106

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.conePts_of_chartIdeal {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ) (hy : ∀ h ∈ chartIdeal P p, eval y h = 0) :
    y ∈ conePts P ∧ (∀ k, y ⟨k, p k⟩ = 1) ∧ affCoord p y = y := by sorry
