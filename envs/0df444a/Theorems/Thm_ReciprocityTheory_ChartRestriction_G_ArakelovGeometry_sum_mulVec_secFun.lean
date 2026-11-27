-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_mulVec_secFun
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sum_mulVec_secFun
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:00:09.515225+00:00
-- url     : https://prove2.me/theorems/a5295628-ab43-44d4-8098-bbcc87caf074
-- title:
--   Arakelov Geometry: sum mul Vec sec Fun
-- statement:
--   The Arakelov Geometry construction uses the sum mul Vec sec Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L48-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L48-L59

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sum_mulVec_secFun {x : Ix κ → Ω} {n r R : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) (M : Matrix (Fin r) (Fin R) ℤ) (Q : Fin R → MvPolynomial (Ix κ) ℤ)
    (hQ : ∀ p, (Q p).IsHomogeneous n)
    (hM : ∀ p, ∑ j, (M j p : Ω) * aeval x (b j) = aeval x (Q p)) (c : Fin R → ℂ) :
    ∀ z ∈ pts (coordIdeal ℤ x), ∑ j, (M.map (Int.cast : ℤ → ℂ) *ᵥ c) j * secFun (b j) z =
      ∑ p, c p * eval z (map (Int.castRingHom ℂ) (Q p)) := by sorry
