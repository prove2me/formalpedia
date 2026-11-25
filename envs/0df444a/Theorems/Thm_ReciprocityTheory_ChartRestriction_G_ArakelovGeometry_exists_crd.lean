-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_crd
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_crd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:46:36.745961+00:00
-- url     : https://prove2.me/theorems/790021c8-3514-5fda-a70b-8680b8f42435
-- title:
--   Arakelov Geometry: exists crd
-- statement:
--   The Arakelov Geometry construction uses the exists crd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L195-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L195-L213

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_crd {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) :
    ∃ crd : sec ℤ x n →ₗ[ℤ] (Fin r → ℤ),
      (∀ v : sec ℤ x n, ∑ j, (crd v j : Ω) * aeval x (b j) = v) ∧
      ∀ j (h : aeval x (b j) ∈ sec ℤ x n), crd ⟨aeval x (b j), h⟩ = Pi.single j 1 := by sorry
