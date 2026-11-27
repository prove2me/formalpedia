-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_cols_det_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_cols_det_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:39.658721+00:00
-- url     : https://prove2.me/theorems/a5368fd7-94cd-4809-b18a-9b8eb9970b30
-- title:
--   Arakelov Geometry: exists cols det ne zero
-- statement:
--   The Arakelov Geometry construction uses the exists cols det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L47-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L47-L93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_cols_det_ne_zero {r : ℕ} {ι : Type} [Finite ι] (u : ι → Fin r → ℤ)
    (hspan : ∀ v : Fin r → ℤ, v ∈ Submodule.span ℤ (Set.range u)) :
    ∃ f : Fin r → ι, (Matrix.of fun p q => u (f q) p).det ≠ 0 := by sorry
