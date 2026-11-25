-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_pt_lower
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pt_lower
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T16:00:18.964806+00:00
-- url     : https://prove2.me/theorems/0e2c359a-d9e5-4334-96f1-1b4ec45d9e65
-- title:
--   Arakelov Geometry: pt lower
-- statement:
--   The Arakelov Geometry construction uses the pt lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L71-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L71-L125

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pt_lower {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hFS : IsPullFS x e m) {N kε δ : ℕ} (H : Fin δ → MvPolynomial (Ix κ) ℤ) {Cε : ℝ}
    (hCε0 : 0 ≤ Cε)
    (hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ kε)
    (c : Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card) → ℂ) {z : Ix κ → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) :
    ‖∑ p, c p * eval z (map (Int.castRingHom ℂ) (prodForm e (adtEnum D N (finProdFinEquiv.symm p).2)
        (H (finProdFinEquiv.symm p).1)))‖ ^ 2 * wgt m (N + kε) z ≤
      Cε ^ 2 * δ * ((N + D).choose D : ℝ) *
        ∑ l : Fin δ, ∑ i, ‖c (finProdFinEquiv (l, i))‖ ^ 2 * monoNormSq (adtEnum D N i) := by sorry
