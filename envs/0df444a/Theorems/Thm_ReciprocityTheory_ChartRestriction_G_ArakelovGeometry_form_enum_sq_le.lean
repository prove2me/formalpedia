-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_form_enum_sq_le
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.form_enum_sq_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:46:23.677862+00:00
-- url     : https://prove2.me/theorems/a8280b19-0b79-5b63-acbb-9e55ff3bd592
-- title:
--   Arakelov Geometry: form enum sq le
-- statement:
--   The Arakelov Geometry construction uses the form enum sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L138-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L138-L157

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.form_enum_sq_le (D N : ℕ) (c : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℂ)
    (w : Fin (D + 1) → ℂ) :
    ‖∑ i, c i * monoC (adtEnum D N i) w‖ ^ 2 ≤ ((N + D).choose D : ℝ) * sqN w ^ N *
      ∑ i, ‖c i‖ ^ 2 * monoNormSq (adtEnum D N i) := by sorry
