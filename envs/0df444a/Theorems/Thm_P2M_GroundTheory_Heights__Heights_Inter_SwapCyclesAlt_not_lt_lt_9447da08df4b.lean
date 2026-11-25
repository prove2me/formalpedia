-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_lt_lt_9447da08df4b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_lt_lt_9447da08df4b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:35.678804+00:00
-- url     : https://prove2.me/theorems/ec3fe66f-5fed-5af7-9bae-3fda80889a74
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt not lt lt 9447da08df4b: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt not lt lt 9447da08df4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt not lt lt 9447da08df4b construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt not lt lt 9447da08df4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L18-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L18-L50

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_lt_lt_9447da08df4b {R : Type*} [CommRing R] [IsNoetherianRing R] {V W W' : Ideal R} [V.IsPrime]
    [W'.IsPrime] {x : R} (hW : W ∈ (V ⊔ Ideal.span {x}).minimalPrimes) (hVW' : V < W')
    (hW'W : W' < W) : False := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«not_lt_lt» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_lt_lt_9447da08df4b
