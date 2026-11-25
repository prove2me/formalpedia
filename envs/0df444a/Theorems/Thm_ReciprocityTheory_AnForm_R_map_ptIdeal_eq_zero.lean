-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_map_ptIdeal_eq_zero
-- name    : ReciprocityTheory.AnForm.R.map_ptIdeal_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:26.906425+00:00
-- url     : https://prove2.me/theorems/a4f95e40-9031-5f5c-bef0-9af92f55a342
-- title:
--   R: map pt Ideal eq zero
-- statement:
--   The R construction uses the map pt Ideal eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L91-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AnChartA.lean#L91-L108

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

theorem ReciprocityTheory.AnForm.R.map_ptIdeal_eq_zero (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) {e : ℕ}
    (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p))
    (χ : locRing K p →+* DualNumber ℂ)
    (hχ : ∀ i, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) = 0) :
    ∀ x ∈ ptIdeal p, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x) = 0 := by sorry
