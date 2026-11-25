-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_fderiv_bound_compact
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_fderiv_bound_compact
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:58.502591+00:00
-- url     : https://prove2.me/theorems/55b8bb8b-2d19-5af3-a480-16847979358f
-- title:
--   Arakelov Geometry: exists fderiv bound compact
-- statement:
--   The Arakelov Geometry construction uses the exists fderiv bound compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SectionBasisLocalUniformBound.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SectionBasisLocalUniformBound.lean#L20-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionBasisLocalUniformBound
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_fderiv_bound_compact {U K : Set (Fin D → ℂ)} (hU : IsOpen U) {ν : (Fin D → ℂ) → ℝ}
    (hν : ContDiffOn ℝ 1 ν U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ, ∀ y ∈ K, ‖fderiv ℝ ν y‖ ≤ L := by sorry
