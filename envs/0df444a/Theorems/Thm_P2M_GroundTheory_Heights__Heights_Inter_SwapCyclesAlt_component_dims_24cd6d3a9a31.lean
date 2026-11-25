-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_component_dims_24cd6d3a9a31
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_component_dims_24cd6d3a9a31
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:33:27.031715+00:00
-- url     : https://prove2.me/theorems/7027625c-6a2a-5a7f-9e93-6ae223422889
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt component dims 24cd6d3a9a31: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt component dims 24cd6d3a9a31
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt component dims 24cd6d3a9a31 construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt component dims 24cd6d3a9a31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L113-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L113-L138

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_component_dims_24cd6d3a9a31 {P U : Ideal (MRing ι)} [P.IsPrime] {s s' : MRing ι} {m : ℕ}
    (hP : ringKrullDim (MRing ι ⧸ P) = ((m + 2 : ℕ) : WithBot ℕ∞)) (hs : s ∉ P) (hs' : s' ∉ P)
    (hnc : ∀ W, W ∈ divSupp P s → W ∉ divSupp P s') (hUr : IsRelevant U)
    (hU : U ∈ (P ⊔ Ideal.span {s} ⊔ Ideal.span {s'}).minimalPrimes) :
    ringKrullDim (MRing ι ⧸ U) = (m : WithBot ℕ∞) ∧
      (U.map (Ideal.Quotient.mk P)).IsPrime ∧
      ∀ [(U.map (Ideal.Quotient.mk P)).IsPrime],
        ringKrullDim (Localization.AtPrime (U.map (Ideal.Quotient.mk P))) = 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«component_dims» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_component_dims_24cd6d3a9a31
