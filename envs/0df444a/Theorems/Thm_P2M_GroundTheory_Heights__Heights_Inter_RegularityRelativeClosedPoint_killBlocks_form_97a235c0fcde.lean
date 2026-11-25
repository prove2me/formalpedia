-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_form_97a235c0fcde
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_form_97a235c0fcde
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:01:18.083951+00:00
-- url     : https://prove2.me/theorems/04737612-0010-4842-b0c1-bf5e802c27d7
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point kill Blocks form 97a235c0fcde: P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point kill Blocks form 97
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point kill Blocks form 97a235c0fcde construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Relative Closed Point kill Blocks form 97a235c0fcde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLeRingKrullDim.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLeRingKrullDim.lean#L20-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLeRingKrullDim
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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_form_97a235c0fcde (S : Finset K) {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) :
    killBlocks S g = (∏ k, (if k ∈ S then (0 : MRing ι) else 1) ^ a k) * g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityRelativeClosedPoint».«killBlocks_form» := P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_form_97a235c0fcde
