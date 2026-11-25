-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_maDensity_nonneg_of
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_nonneg_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:40.953599+00:00
-- url     : https://prove2.me/theorems/dca63717-769f-4a48-9830-7a33cf2688d4
-- title:
--   Arakelov Geometry: adens ma Density nonneg of
-- statement:
--   The Arakelov Geometry construction uses the adens ma Density nonneg of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L75-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L75-L89

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_nonneg_of {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {V : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (hV : IsOpen V) (hγ : AnalyticOnNhd ℂ γ V)
    (hpts : ∀ y ∈ V, γ y ∈ pts P) {y : Fin D → ℂ} (hy : y ∈ V) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by sorry
