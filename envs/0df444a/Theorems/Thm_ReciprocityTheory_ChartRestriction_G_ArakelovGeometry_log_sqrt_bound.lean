-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_log_sqrt_bound
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.log_sqrt_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:39:15.665484+00:00
-- url     : https://prove2.me/theorems/76ec1dc1-9e20-408a-b09e-90632646baa3
-- title:
--   Arakelov Geometry: log sqrt bound
-- statement:
--   The Arakelov Geometry construction uses the log sqrt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStC.lean#L37-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStC.lean#L37-L65

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.log_sqrt_bound (D : ℕ) {T : ℝ} (hT : 1 ≤ T) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log (Real.sqrt (T * (n : ℝ) ^ D)) ∧
      Real.log (Real.sqrt (T * (n : ℝ) ^ D)) ≤
        (1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1) := by sorry
