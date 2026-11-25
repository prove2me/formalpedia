-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sec_le_span_prod
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sec_le_span_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T16:00:47.342783+00:00
-- url     : https://prove2.me/theorems/a95efd35-4107-4b04-a5f8-417005204ffc
-- title:
--   Arakelov Geometry: sec le span prod
-- statement:
--   The Arakelov Geometry construction uses the sec le span prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L160-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L160-L185

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sec_le_span_prod {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {n k₀ r₀ : ℕ}
    (hmul : sec ℤ x n = sec ℤ (x ∘ e) (n - k₀) * sec ℤ x k₀) {tb : Fin r₀ → MvPolynomial (Ix κ) ℚ}
    (htb : IsSecBasis x k₀ tb) (Tf : Fin r₀ → MvPolynomial (Ix κ) ℤ)
    (hTfb : ∀ i, tb i = map (Int.castRingHom ℚ) (Tf i)) :
    sec ℤ x n ≤ Submodule.span ℤ (Set.range fun s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card ×
      Fin r₀ => aeval x (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2))) := by sorry
