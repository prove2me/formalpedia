-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_psd_sub_of_quad_le
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.psd_sub_of_quad_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:17.677838+00:00
-- url     : https://prove2.me/theorems/aec9c0ad-9227-47e8-a62d-e40cf60cd8ce
-- title:
--   Arakelov Geometry: psd sub of quad le
-- statement:
--   The Arakelov Geometry construction uses the psd sub of quad le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean#L154-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean#L154-L164

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.psd_sub_of_quad_le {r : ℕ} {P Q : Matrix (Fin r) (Fin r) ℂ} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) (h : ∀ c : Fin r → ℂ, (star c ⬝ᵥ Q *ᵥ c).re ≤ (star c ⬝ᵥ P *ᵥ c).re) :
    (P - Q).PosSemidef := by sorry
