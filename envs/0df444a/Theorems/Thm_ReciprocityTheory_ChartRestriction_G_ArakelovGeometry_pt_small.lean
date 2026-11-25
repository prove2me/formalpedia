-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_pt_small
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pt_small
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:58:52.152558+00:00
-- url     : https://prove2.me/theorems/54b9f166-18a1-5a55-8cc8-529df95f07d8
-- title:
--   Arakelov Geometry: pt small
-- statement:
--   The Arakelov Geometry construction uses the pt small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L127-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L127-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStE
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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pt_small {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hFS : IsPullFS x e m) {N k₀ : ℕ} {a : Fin (D + 1) → ℕ} (ha : ∑ t, a t = N)
    (t : MvPolynomial (Ix κ) ℤ) {Ct : ℝ}
    (hCt : ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z (map (Int.castRingHom ℂ) t)‖ ≤ Ct * m.ρ z ^ k₀)
    {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    ‖eval z (map (Int.castRingHom ℂ) (prodForm e a t))‖ ^ 2 * wgt m (N + k₀) z ≤ Ct ^ 2 := by sorry
