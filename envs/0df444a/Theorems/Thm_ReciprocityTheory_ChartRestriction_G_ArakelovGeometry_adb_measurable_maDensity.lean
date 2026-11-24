-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adb_measurable_maDensity
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:34.974806+00:00
-- url     : https://prove2.me/theorems/116d49d4-339b-4015-a82b-5e4648424d77
-- title:
--   Arakelov Geometry: adb measurable ma Density
-- statement:
--   The Arakelov Geometry construction uses the adb measurable ma Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStBA.lean#L127-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStBA.lean#L127-L135

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Topology
open scoped ComplexOrder
variable {κ : Type} [Fintype κ] {D : ℕ}
variable {P : Ideal (MRing (GlobalTheory κ))} {Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)}
  {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity (φ : Fin D → (Fin D → ℂ) → ℝ) : Measurable (maDensity φ) := by sorry
