-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_sup_0626960bf546
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_sup_0626960bf546
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:08.24188+00:00
-- url     : https://prove2.me/theorems/39ecb2b2-e19a-4a88-818e-78116ae0fea3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt mem minimal Primes sup 0626960bf546: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt mem minimal Primes sup 0626960bf546
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt mem minimal Primes sup 0626960bf546 construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt mem minimal Primes sup 0626960bf546 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L65-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSwapCycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
  ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_sup_0626960bf546 {R : Type*} [CommRing R] {V W Z : Ideal R} {f t : R}
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes)
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hWZ : W ≤ Z) :
    Z ∈ (W ⊔ Ideal.span {t}).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«mem_minimalPrimes_sup» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_sup_0626960bf546
