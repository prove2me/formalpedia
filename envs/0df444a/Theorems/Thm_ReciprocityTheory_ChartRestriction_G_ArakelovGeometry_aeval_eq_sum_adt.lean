-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_eq_sum_adt
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_eq_sum_adt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:52.010745+00:00
-- url     : https://prove2.me/theorems/b52c3b1e-2a77-49a9-b1c2-f8482fc120bd
-- title:
--   Arakelov Geometry: aeval eq sum adt
-- statement:
--   The Arakelov Geometry construction uses the aeval eq sum adt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStA.lean#L14-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStA.lean#L14-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CNormSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_HadZSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
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
open scoped ComplexOrder

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_eq_sum_adt {D N : ℕ} {S : Type*} [CommRing S] (g : MvPolynomial (Fin (D + 1)) ℤ)
    (hg : g.IsHomogeneous N) (y : Fin (D + 1) → S) :
    aeval y g = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
      ((coeff (Finsupp.equivFunOnFinite.symm a) g : ℤ) : S) * ∏ i, y i ^ a i := by sorry
