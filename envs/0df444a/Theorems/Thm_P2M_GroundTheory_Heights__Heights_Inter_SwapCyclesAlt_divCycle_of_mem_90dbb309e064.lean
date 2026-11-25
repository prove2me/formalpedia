-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_of_mem_90dbb309e064
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_of_mem_90dbb309e064
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:30.838051+00:00
-- url     : https://prove2.me/theorems/e0c9b68d-ee40-4168-af73-0937bc8b7582
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt div Cycle of mem 90dbb309e064: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt div Cycle of mem 90dbb309e064
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt div Cycle of mem 90dbb309e064 construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt div Cycle of mem 90dbb309e064 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L140-L143

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_of_mem_90dbb309e064 {V W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∈ divSupp V f) :
    divCycle V f W = multAt (V ⊔ Ideal.span {f}) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«divCycle_of_mem» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_of_mem_90dbb309e064
