-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_locRing_isLocalRing_isNoetherian
-- name    : ReciprocityTheory.AnForm.R.locRing_isLocalRing_isNoetherian
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:02.770359+00:00
-- url     : https://prove2.me/theorems/40502e17-3a8b-4c47-ae42-dd664ba8e590
-- title:
--   R: loc Ring is Local Ring is Noetherian
-- statement:
--   The R construction uses the loc Ring is Local Ring is Noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChart.lean#L30-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChart.lean#L30-L45

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

theorem ReciprocityTheory.AnForm.R.locRing_isLocalRing_isNoetherian (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) : IsLocalRing (locRing K p) ∧ IsNoetherianRing (locRing K p) := by sorry
