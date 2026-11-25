-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_quad_conj
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.quad_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:36:04.067449+00:00
-- url     : https://prove2.me/theorems/f4f92da0-f277-4a2d-9ea7-4e73596a6fec
-- title:
--   Arakelov Geometry: quad conj
-- statement:
--   The Arakelov Geometry construction uses the quad conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean#L175-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean#L175-L178

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
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
open Matrix

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.quad_conj {r s : ℕ} (M : Matrix (Fin s) (Fin r) ℂ) (G : Matrix (Fin s) (Fin s) ℂ)
    (c : Fin r → ℂ) :
    star c ⬝ᵥ (Mᴴ * G * M) *ᵥ c = star (M *ᵥ c) ⬝ᵥ G *ᵥ (M *ᵥ c) := by sorry
