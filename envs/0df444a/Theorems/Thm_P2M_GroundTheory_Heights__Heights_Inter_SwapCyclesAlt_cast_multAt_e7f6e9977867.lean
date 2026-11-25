-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_cast_multAt_e7f6e9977867
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_cast_multAt_e7f6e9977867
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:41.492462+00:00
-- url     : https://prove2.me/theorems/83944395-cef0-4046-870d-b27f3717f766
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt cast mult At e7f6e9977867: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt cast mult At e7f6e9977867
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt cast mult At e7f6e9977867 construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt cast mult At e7f6e9977867 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L155-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L155-L159

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSwapCycles
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_cast_multAt

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_cast_multAt_e7f6e9977867 {J W : Ideal (MRing ι)} [hW : W.IsPrime] (hJ : W ∈ J.minimalPrimes) :
    ((multAt J W : ℕ) : ℕ∞) = lenAt J W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«cast_multAt» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_cast_multAt_e7f6e9977867
