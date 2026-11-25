-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_comp_eb0db3f96410
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_comp_eb0db3f96410
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:45:42.905956+00:00
-- url     : https://prove2.me/theorems/18cbeec3-e873-49df-b768-3ad8b9e70367
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point kill Blocks comp eb0db3f96410: P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point kill Blocks comp eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point kill Blocks comp eb0db3f96410 construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point kill Blocks comp eb0db3f96410 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLeRingKrullDim.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLeRingKrullDim.lean#L42-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLeRingKrullDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_killBlocks_comp_73c8076a9a36

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_comp_eb0db3f96410 {S T : Finset K} (hST : S ⊆ T) :
    (killBlocks T).comp (killBlocks S) = (killBlocks T : MRing ι →ₐ[ℤ] MRing ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityRelativeClosedPoint».«killBlocks_comp» := P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_comp_eb0db3f96410
