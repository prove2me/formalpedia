-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_le_comap_killBlocks_6f4593612eea
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_le_comap_killBlocks_6f4593612eea
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:30.63637+00:00
-- url     : https://prove2.me/theorems/d19bd274-bd28-4423-a9fb-3910b2bd6988
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point le comap kill Blocks 6f4593612eea: P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point le comap kill B
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point le comap kill Blocks 6f4593612eea construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point le comap kill Blocks 6f4593612eea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLeRingKrullDim.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLeRingKrullDim.lean#L31-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLeRingKrullDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_le_comap_killBlocks_2335735e93b1

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_le_comap_killBlocks_6f4593612eea (S : Finset K) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W) :
    W ≤ W.comap (killBlocks S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityRelativeClosedPoint».«le_comap_killBlocks» := P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_le_comap_killBlocks_6f4593612eea
