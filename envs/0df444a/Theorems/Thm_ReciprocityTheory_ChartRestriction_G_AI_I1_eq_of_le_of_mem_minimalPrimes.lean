-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_eq_of_le_of_mem_minimalPrimes
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_le_of_mem_minimalPrimes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:28.445816+00:00
-- url     : https://prove2.me/theorems/2fd8bed6-28d6-43a6-8d72-75a2bcec21aa
-- title:
--   I1: eq of le of mem minimal Primes
-- statement:
--   The I1 construction uses the eq of le of mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L141-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean#L141-L169

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_le_of_mem_minimalPrimes [IsNoetherianRing R] {V W Q : Ideal R} (hV : V.IsPrime) {f g : R}
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hQ : Q.IsPrime) (hVQ : V ≤ Q) (hgQ : g ∈ Q)
    (hgV : g ∉ V) (hQW : Q ≤ W) : Q = W := by sorry
