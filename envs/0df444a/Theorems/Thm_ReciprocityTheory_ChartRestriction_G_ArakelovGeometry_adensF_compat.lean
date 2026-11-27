-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adensF_compat
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adensF_compat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:20:23.906247+00:00
-- url     : https://prove2.me/theorems/e998915a-b20b-44e5-9d59-57ead02c2c1b
-- title:
--   Arakelov Geometry: adens F compat
-- statement:
--   The Arakelov Geometry construction uses the adens F compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L133-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L133-L150

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder
variable {J : Type} [Fintype J] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adensF_compat {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J} {μ : Measure (J → ℂ)}
    (hsm : IsSmoothMetric m) {U U' : Set (Fin D → ℂ)} {γ γ' : (Fin D → ℂ) → J → ℂ}
    {ν ν' : (Fin D → ℂ) → ℝ} (h : IsParam P U γ) (hν : IsDensityFor μ U γ ν)
    (h' : IsParam P U' γ') (hν' : IsDensityFor μ U' γ' ν')
    {O' : Set (J → ℂ)} {q' : (J → ℂ) → Fin D → ℂ} (hO' : IsOpen O') (hq' : AnalyticOnNhd ℂ q' O')
    (hOP' : O' ∩ pts P = coneOver U' γ')
    (hsc' : ∀ z ∈ O', ∀ c : ℂ, c ≠ 0 → c • z ∈ O' ∧ q' (c • z) = q' z)
    (hqγ' : ∀ y ∈ U', q' (γ' y) = y) {y : Fin D → ℂ} (hy : y ∈ U) (hyO : γ y ∈ O') :
    adensF m γ' ν' (q' (γ y)) * ((D.factorial : ℝ) * ν y) =
      maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by sorry
