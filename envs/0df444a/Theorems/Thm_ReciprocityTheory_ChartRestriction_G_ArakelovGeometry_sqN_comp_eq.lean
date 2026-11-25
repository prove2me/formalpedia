-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sqN_comp_eq
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sqN_comp_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:14.8923+00:00
-- url     : https://prove2.me/theorems/9cb7d701-ac2f-475b-b33b-858b368ad41b
-- title:
--   Arakelov Geometry: sq N comp eq
-- statement:
--   The Arakelov Geometry construction uses the sq N comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L257-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L257-L261

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sqN_comp_eq {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hFS : IsPullFS x e m) {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    sqN (z ∘ e) = m.ρ z ^ 2 := by sorry
