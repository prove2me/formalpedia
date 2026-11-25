-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_param_of_cut
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_param_of_cut
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:08:51.350995+00:00
-- url     : https://prove2.me/theorems/e2214e16-0ed2-472e-8e0d-0779198a4a63
-- title:
--   Arakelov Geometry: gbap param of cut
-- statement:
--   The Arakelov Geometry construction uses the gbap param of cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStB.lean#L20-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStB.lean#L20-L225

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_param_of_cut {D c : ℕ} (Z : Set (Fin (D + 1 + c) → ℂ))
    (hZc : ∀ z ∈ Z, ∀ t : ℂ, t ≠ 0 → t • z ∈ Z)
    (F : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ) (h : MvPolynomial (Fin (D + 1 + c)) ℂ)
    (hZ : ∀ z, z ≠ 0 → eval z h ≠ 0 → (z ∈ Z ↔ ∀ i, eval z (F i) = 0))
    (p : Fin (D + 1 + c) → ℂ) (hp : p ∈ Z) (hp0 : p ≠ 0) (hph : eval p h ≠ 0)
    (hjac : Function.Surjective (fun v : Fin (D + 1 + c) → ℂ =>
      fun i => ∑ j, eval p (pderiv j (F i)) * v j)) :
    ∃ (ρ₀ : ℝ) (γ : (Fin D → ℂ) → Fin (D + 1 + c) → ℂ), 0 < ρ₀ ∧
      AnalyticOnNhd ℂ γ (Metric.ball 0 ρ₀) ∧ (∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, γ y ∈ Z) ∧
      (∃ (O : Set (Fin (D + 1 + c) → ℂ)) (q : (Fin (D + 1 + c) → ℂ) → Fin D → ℂ), IsOpen O ∧
        AnalyticOnNhd ℂ q O ∧ O ∩ Z = coneOver (Metric.ball 0 ρ₀) γ ∧
        (∀ z ∈ O, ∀ t : ℂ, t ≠ 0 → t • z ∈ O ∧ q (t • z) = q z) ∧
        ∀ y ∈ Metric.ball 0 ρ₀, q (γ y) = y) ∧ γ 0 = p := by sorry
