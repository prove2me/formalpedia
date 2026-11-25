-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_maDensity_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_nonneg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:56.710612+00:00
-- url     : https://prove2.me/theorems/a84bf3fc-c999-597d-899a-d905ae1d1c38
-- title:
--   Arakelov Geometry: adens ma Density nonneg
-- statement:
--   The Arakelov Geometry construction uses the adens ma Density nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L100-L104

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_nonneg {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (h : IsParam P U γ) {y : Fin D → ℂ} (hy : y ∈ U) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by sorry
