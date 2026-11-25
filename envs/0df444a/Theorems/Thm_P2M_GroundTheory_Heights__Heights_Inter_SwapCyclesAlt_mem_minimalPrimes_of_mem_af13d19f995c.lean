-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_of_mem_af13d19f995c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_of_mem_af13d19f995c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:18.129742+00:00
-- url     : https://prove2.me/theorems/c7f472f4-263c-42af-a222-c70103ec31f5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt mem minimal Primes of mem af13d19f995c: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt mem minimal Primes of mem af13d19f995c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt mem minimal Primes of mem af13d19f995c construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt mem minimal Primes of mem af13d19f995c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L52-L63

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_of_mem_af13d19f995c {R : Type*} [CommRing R] [IsNoetherianRing R] {P W : Ideal R}
    [P.IsPrime] {a b : R} (hW : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes) (hbP : b ∉ P)
    (hbW : b ∈ W) : W ∈ (P ⊔ Ideal.span {b}).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«mem_minimalPrimes_of_mem» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_of_mem_af13d19f995c
