-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_eq_zero_of_lt_two_494966552092
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_eq_zero_of_lt_two_494966552092
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:30.63073+00:00
-- url     : https://prove2.me/theorems/63a02452-630c-464a-bbba-a8116413994e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt div Cycle eq zero of lt two 494966552092: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt div Cycle eq zero of lt two 494966552092
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt div Cycle eq zero of lt two 494966552092 construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt div Cycle eq zero of lt two 494966552092 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L272-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L272-L295

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_eq_zero_of_lt_two_494966552092 {P W : Ideal (MRing ι)} [P.IsPrime] {b b' : MRing ι}
    {c c' : K → ℕ} {d : ℕ} (hPmh : IsMultiHomogIdeal P)
    (hPd : ringKrullDim (MRing ι ⧸ P) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) (hd : d < 2)
    (hb : IsMultiHomog b c) (hb' : IsMultiHomog b' c') (hbP : b ∉ P) (hW : W ∈ divSupp P b)
    (hb'W : b' ∉ W) : divCycle W b' = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«divCycle_eq_zero_of_lt_two» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_eq_zero_of_lt_two_494966552092
