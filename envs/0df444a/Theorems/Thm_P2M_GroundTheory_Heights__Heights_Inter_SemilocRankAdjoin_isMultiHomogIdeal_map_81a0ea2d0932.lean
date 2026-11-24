-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_isMultiHomogIdeal_map_81a0ea2d0932
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_isMultiHomogIdeal_map_81a0ea2d0932
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:23.027688+00:00
-- url     : https://prove2.me/theorems/bb26bd85-24bf-416e-ba05-b7eb6afd0d8e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin is Multi Homog Ideal map 81a0ea2d0932: P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin is Multi Homog Ideal map 81a0ea2d0932
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin is Multi Homog Ideal map 81a0ea2d0932 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Rank Adjoin is Multi Homog Ideal map 81a0ea2d0932 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankAdjoin.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankAdjoin.lean#L19-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PAdjoinIndepRelfinrank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFinrankAdjoinRange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_isMultiHomogIdeal_map_81a0ea2d0932 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℚ) : MRing ι →+* MRingOver ℚ ι)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocRankAdjoin».«isMultiHomogIdeal_map» := P2M_GroundTheory_Heights__Heights_Inter_SemilocRankAdjoin_isMultiHomogIdeal_map_81a0ea2d0932
