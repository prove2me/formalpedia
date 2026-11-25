-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_crd_span
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.crd_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:16.080504+00:00
-- url     : https://prove2.me/theorems/0f35a2bc-7420-4675-9471-d7e6d6af36b9
-- title:
--   Arakelov Geometry: crd span
-- statement:
--   The Arakelov Geometry construction uses the crd span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L215-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L215-L246

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.crd_span {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    {crd : sec ℤ x n →ₗ[ℤ] (Fin r → ℤ)}
    (hcrd : ∀ j (h : aeval x (b j) ∈ sec ℤ x n), crd ⟨aeval x (b j), h⟩ = Pi.single j 1)
    (hb : IsSecBasis x n b) {ι : Type} (w : ι → Ω) (hw : ∀ s, w s ∈ sec ℤ x n)
    (hle : sec ℤ x n ≤ Submodule.span ℤ (Set.range w)) (v : Fin r → ℤ) :
    v ∈ Submodule.span ℤ (Set.range fun s => crd ⟨w s, hw s⟩) := by sorry
