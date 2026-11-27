-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isHermitian_sq_smul
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isHermitian_sq_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:21:55.541806+00:00
-- url     : https://prove2.me/theorems/3927210e-7e27-517c-9faa-25d1bf7fd15e
-- title:
--   Arakelov Geometry: is Hermitian sq smul
-- statement:
--   The Arakelov Geometry construction uses the is Hermitian sq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean#L167-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean#L167-L172

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isHermitian_sq_smul {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian) (A : ℝ) :
    (((A : ℂ) ^ 2) • G).IsHermitian := by sorry
