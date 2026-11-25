-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_trace_sup_le
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.trace_sup_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:06:37.637842+00:00
-- url     : https://prove2.me/theorems/0f1b7311-29fd-4ad3-9a8c-98c3a2a586a3
-- title:
--   Arakelov Geometry: trace sup le
-- statement:
--   The Arakelov Geometry construction uses the trace sup le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CNormSt.lean#L89-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CNormSt.lean#L89-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupLeL2NormSections
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CNormSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.trace_sup_le {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    {n r : ℕ} (f : Fin r → MvPolynomial (Ix κ) ℤ) (g : Fin r → MvPolynomial (Fin (D + 1)) ℤ)
    (hf : ∀ k, (f k).IsHomogeneous n) (hgh : ∀ k, (g k).IsHomogeneous n)
    (htr : ∀ k, aeval (x ∘ e) (g k) = secTrace x e n (aeval x (f k))) (c : Fin r → ℂ) {S : ℝ}
    (hS : ∀ z ∈ pts (coordIdeal ℤ x),
      ‖∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k))‖ ≤ S * m.ρ z ^ n)
    (w : Fin (D + 1) → ℂ) :
    ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ ≤
      (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ n := by sorry
