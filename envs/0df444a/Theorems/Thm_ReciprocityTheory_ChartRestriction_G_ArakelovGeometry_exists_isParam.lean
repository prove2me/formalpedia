-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_isParam
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_isParam
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:00.671535+00:00
-- url     : https://prove2.me/theorems/17eb2f8f-9d94-4c8f-9986-c7f47611c92f
-- title:
--   Arakelov Geometry: exists is Param
-- statement:
--   The Arakelov Geometry construction uses the exists is Param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamSt.lean#L26-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamSt.lean#L26-L126

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
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
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_isParam {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {z₀ : Ix κ → ℂ} (hz₀ : z₀ ∈ pts (coordIdeal ℤ x)) :
    ∃ (ρ₀ : ℝ) (γ : (Fin D → ℂ) → Ix κ → ℂ), 0 < ρ₀ ∧
      IsParam (coordIdeal ℤ x) (Metric.ball 0 ρ₀) γ ∧ γ 0 = z₀ := by sorry
