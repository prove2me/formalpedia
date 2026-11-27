-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adensF_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adensF_nonneg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:20:18.376728+00:00
-- url     : https://prove2.me/theorems/d8d9ce2b-65d0-4111-b587-a1a123866362
-- title:
--   Arakelov Geometry: adens F nonneg
-- statement:
--   The Arakelov Geometry construction uses the adens F nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L152-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L152-L158

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adensF_nonneg {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J} {μ : Measure (J → ℂ)}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) {y : Fin D → ℂ} (hy : y ∈ U) : 0 ≤ adensF m γ ν y := by sorry
