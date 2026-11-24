-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_dim_of_mem_minimalPrimes_45eaf6f19df9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_dim_of_mem_minimalPrimes_45eaf6f19df9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:35.561081+00:00
-- url     : https://prove2.me/theorems/5b3fbae6-0e4f-44d1-b25f-8466a3bb046e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt dim of mem minimal Primes 45eaf6f19df9: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt dim of mem minimal Primes 45eaf6f19df9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt dim of mem minimal Primes 45eaf6f19df9 construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt dim of mem minimal Primes 45eaf6f19df9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L77-L81

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_dim_of_mem_minimalPrimes_45eaf6f19df9 {P W : Ideal (MRing ι)} [P.IsPrime] {s : MRing ι} {m : ℕ}
    (hP : ringKrullDim (MRing ι ⧸ P) = ((m + 1 : ℕ) : WithBot ℕ∞)) (hs : s ∉ P)
    (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) :
    ringKrullDim (MRing ι ⧸ W) = (m : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«dim_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_dim_of_mem_minimalPrimes_45eaf6f19df9
