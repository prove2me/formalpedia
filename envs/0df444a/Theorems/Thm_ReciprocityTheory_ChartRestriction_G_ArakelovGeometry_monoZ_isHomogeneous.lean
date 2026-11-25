-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_monoZ_isHomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.monoZ_isHomogeneous
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:18.017524+00:00
-- url     : https://prove2.me/theorems/e2072bcf-a3f2-4e67-a361-bc6cb136199d
-- title:
--   Arakelov Geometry: mono Z is Homogeneous
-- statement:
--   The Arakelov Geometry construction uses the mono Z is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L162-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L162-L167

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.monoZ_isHomogeneous {N d : ℕ} {a : Fin N → ℕ} (ha : ∑ i, a i = d) :
    (monoZ a).IsHomogeneous d := by sorry
