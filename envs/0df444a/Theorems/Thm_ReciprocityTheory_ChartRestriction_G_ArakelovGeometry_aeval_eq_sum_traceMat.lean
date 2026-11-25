-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_eq_sum_traceMat
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_eq_sum_traceMat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:21:18.436542+00:00
-- url     : https://prove2.me/theorems/08a98a97-580b-571e-adff-25089069d26b
-- title:
--   Arakelov Geometry: aeval eq sum trace Mat
-- statement:
--   The Arakelov Geometry construction uses the aeval eq sum trace Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean#L22-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStB.lean#L22-L58

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_eq_sum_traceMat {S : Type*} [CommRing S] {r δ N : ℕ}
    (g : Fin r → Fin δ → MvPolynomial (Fin (D + 1)) ℤ) (j : Fin r) (l : Fin δ)
    (hg : (g j l).IsHomogeneous N) (y : Fin (D + 1) → S) :
    aeval y (g j l) = ∑ i, ((traceMat D N g (finProdFinEquiv (l, i)) j : ℤ) : S) *
      ∏ t, y t ^ adtEnum D N i t := by sorry
