-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_apply_eq_fd07f7c3f991
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_apply_eq_fd07f7c3f991
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:38.651551+00:00
-- url     : https://prove2.me/theorems/b5df5aad-b4ca-4726-8754-785541e87930
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt sum apply eq fd07f7c3f991: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt sum apply eq fd07f7c3f991
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt sum apply eq fd07f7c3f991 construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt sum apply eq fd07f7c3f991 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L161-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L161-L170

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_apply_eq_fd07f7c3f991 (V Z : Ideal (MRing ι)) (f t : MRing ι) :
    ((divCycle V f).sum fun W m => m • divCycle W t) Z =
      ∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«sum_apply_eq» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_apply_eq_fd07f7c3f991
