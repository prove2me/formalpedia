-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_jacobian_cut
-- name    : ReciprocityTheory.AnForm.R.exists_jacobian_cut
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:10.205073+00:00
-- url     : https://prove2.me/theorems/63894469-89fb-4691-b011-46f6d1a79784
-- title:
--   R: exists jacobian cut
-- statement:
--   The R construction uses the exists jacobian cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChart.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChart.lean#L53-L59

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

theorem ReciprocityTheory.AnForm.R.exists_jacobian_cut (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ)
    [IsRegularLocalRing (locRing K p)] (he : ringKrullDim (locRing K p) = e) :
    e ≤ n ∧ ∃ F : Fin (n - e) → MvPolynomial (Fin n) ℂ, (∀ i, F i ∈ K) ∧
      LinearIndependent ℂ (fun i => grad p (F i)) ∧
      ∃ h : MvPolynomial (Fin n) ℂ, eval p h ≠ 0 ∧ ∀ g ∈ K, h * g ∈ Ideal.span (Set.range F) := by sorry
