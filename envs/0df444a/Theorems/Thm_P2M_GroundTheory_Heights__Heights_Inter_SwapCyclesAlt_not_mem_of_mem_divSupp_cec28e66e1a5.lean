-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_mem_of_mem_divSupp_cec28e66e1a5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_mem_of_mem_divSupp_cec28e66e1a5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:52.995803+00:00
-- url     : https://prove2.me/theorems/80b0f494-f0bf-4b72-9856-a122adbaebc3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt not mem of mem div Supp cec28e66e1a5: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt not mem of mem div Supp cec28e66e1a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt not mem of mem div Supp cec28e66e1a5 construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt not mem of mem div Supp cec28e66e1a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L83-L86

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_mem_of_mem_divSupp_cec28e66e1a5 {P W : Ideal (MRing ι)} [P.IsPrime] {s s' : MRing ι}
    (hs' : s' ∉ P) (hnc : ∀ W, W ∈ divSupp P s → W ∉ divSupp P s') (hW : W ∈ divSupp P s) :
    s' ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«not_mem_of_mem_divSupp» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_mem_of_mem_divSupp_cec28e66e1a5
