-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_map_mk_mem_minimalPrimes
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.map_mk_mem_minimalPrimes
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:52.897806+00:00
-- url     : https://prove2.me/theorems/f5e0e5e1-130e-50bd-9c92-90c7313e6ebc
-- title:
--   I1: map mk mem minimal Primes
-- statement:
--   The I1 construction uses the map mk mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L129-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L129-L134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.map_mk_mem_minimalPrimes {V W : Ideal R} {f : R} (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) :
    W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by sorry
