-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_choose_bound
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.choose_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:35:05.493882+00:00
-- url     : https://prove2.me/theorems/8eb2c3b2-42ec-572d-aeab-fa2b07716143
-- title:
--   Arakelov Geometry: choose bound
-- statement:
--   The Arakelov Geometry construction uses the choose bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStC.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStC.lean#L67-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.choose_bound (k D : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (((n + k + D).choose D : ℕ) : ℝ) ≤ ((1 + k + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by sorry
