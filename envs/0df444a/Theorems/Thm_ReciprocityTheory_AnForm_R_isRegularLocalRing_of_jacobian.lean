-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isRegularLocalRing_of_jacobian
-- name    : ReciprocityTheory.AnForm.R.isRegularLocalRing_of_jacobian
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:35.79875+00:00
-- url     : https://prove2.me/theorems/d568fe69-b2c6-4ffb-8bd8-c8cb3b436036
-- title:
--   R: is Regular Local Ring of jacobian
-- statement:
--   The R construction uses the is Regular Local Ring of jacobian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChart.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChart.lean#L61-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
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

theorem ReciprocityTheory.AnForm.R.isRegularLocalRing_of_jacobian (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hF : ∀ i, F i ∈ K)
    (hlin : LinearIndependent ℂ (fun i => grad p (F i)))
    (hq : ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptIdeal p ∧ 𝔮.height ≤ c) :
    IsRegularLocalRing (locRing K p) ∧ ringKrullDim (locRing K p) = ((n - c : ℕ) : WithBot ℕ∞) := by sorry
