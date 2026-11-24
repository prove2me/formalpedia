-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isGood_interp
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isGood_interp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:35.194938+00:00
-- url     : https://prove2.me/theorems/567831e0-f847-4a26-9644-32920791271e
-- title:
--   Arakelov Geometry: is Good interp
-- statement:
--   The Arakelov Geometry construction uses the is Good interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AInterpSt.lean#L33-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AInterpSt.lean#L33-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isGood_interp {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg₀ : IsGood D x m₀ μ) (hg₁ : IsGood D x m₁ μ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsGood D x (interp m₀ m₁ t) μ := by sorry
