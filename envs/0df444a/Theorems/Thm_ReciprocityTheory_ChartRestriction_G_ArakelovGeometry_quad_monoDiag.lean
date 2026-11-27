-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_quad_monoDiag
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.quad_monoDiag
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:13.957093+00:00
-- url     : https://prove2.me/theorems/a97a9236-e7e1-5b63-80a6-bfe5f5d06fec
-- title:
--   Arakelov Geometry: quad mono Diag
-- statement:
--   The Arakelov Geometry construction uses the quad mono Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean#L181-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean#L181-L193

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.quad_monoDiag (D N δ : ℕ) (v : Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card) → ℂ) :
    (star v ⬝ᵥ monoDiag D N δ *ᵥ v).re =
      ∑ l : Fin δ, ∑ i, monoNormSq (adtEnum D N i) * ‖v (finProdFinEquiv (l, i))‖ ^ 2 := by sorry
