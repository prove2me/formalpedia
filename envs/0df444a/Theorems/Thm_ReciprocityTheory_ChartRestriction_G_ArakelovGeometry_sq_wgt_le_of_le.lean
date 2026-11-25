-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sq_wgt_le_of_le
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sq_wgt_le_of_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:08.592005+00:00
-- url     : https://prove2.me/theorems/b82c7f71-c217-455f-a62a-2e8d2e800a0d
-- title:
--   Arakelov Geometry: sq wgt le of le
-- statement:
--   The Arakelov Geometry construction uses the sq wgt le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L248-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L248-L255

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sq_wgt_le_of_le {m : ConeMetric ℂ (Ix κ)} {n : ℕ} {z : Ix κ → ℂ} (hz : z ≠ 0) {a Y : ℝ}
    (ha : 0 ≤ a) (h : a ≤ Y * m.ρ z ^ n) : a ^ 2 * wgt m n z ≤ Y ^ 2 := by sorry
