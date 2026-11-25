-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_adtEnum
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sum_adtEnum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:16:57.664153+00:00
-- url     : https://prove2.me/theorems/75fc8ffc-ca55-55db-9d65-1c1bf67d7ec0
-- title:
--   Arakelov Geometry: sum adt Enum
-- statement:
--   The Arakelov Geometry construction uses the sum adt Enum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStA.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStA.lean#L57-L60

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sum_adtEnum {M : Type*} [AddCommMonoid M] (D N : ℕ) (f : (Fin (D + 1) → ℕ) → M) :
    ∑ i, f (adtEnum D N i) = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, f a := by sorry
