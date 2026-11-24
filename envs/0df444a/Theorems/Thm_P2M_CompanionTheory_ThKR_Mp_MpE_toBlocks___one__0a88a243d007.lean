-- Prove2me | Theorems.Thm_P2M_CompanionTheory_ThKR_Mp_MpE_toBlocks___one__0a88a243d007
-- name    : P2M_CompanionTheory_ThKR_Mp_MpE_toBlocks___one__0a88a243d007
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:21.881748+00:00
-- url     : https://prove2.me/theorems/352eaad0-dbde-49c4-86e6-739c04e09827
-- title:
--   P2 M Companion Theory Th KR Mp Mp E to Blocks   one  0a88a243d007: P2 M Companion Theory Th KR Mp Mp E to Blocks   one  0a88a243d007
-- statement:
--   The P2 M Companion Theory Th KR Mp Mp E to Blocks   one  0a88a243d007 construction uses the P2 M Companion Theory Th KR Mp Mp E to Blocks   one  0a88a243d007 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticGroupT2Space.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticGroupT2Space.lean#L15-L17

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.MpE
omit [Fintype l]

theorem P2M_CompanionTheory_ThKR_Mp_MpE_toBlocks___one__0a88a243d007 : (1 : Mat l).toBlocks₁₁ = 1 := by sorry

alias «CompanionTheory».«ThKR».«Mp».«MpE».«toBlocks₁₁_one'» := P2M_CompanionTheory_ThKR_Mp_MpE_toBlocks___one__0a88a243d007
