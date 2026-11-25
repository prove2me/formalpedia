-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
-- name    : P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:39.125793+00:00
-- url     : https://prove2.me/theorems/e76dc259-5152-4bcd-9b43-483a1c40cc05
-- title:
--   P2 M Ground Theory Group Coh aug SES obj X  f61122e4f661: P2 M Ground Theory Group Coh aug SES obj X  f61122e4f661
-- statement:
--   The P2 M Ground Theory Group Coh aug SES obj X  f61122e4f661 construction uses the P2 M Ground Theory Group Coh aug SES obj X  f61122e4f661 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L302-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L302-L302

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}

theorem P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661 (X : Rep.{u} k G) : ((augSES k G).obj X).X₃ = X := by sorry

alias «GroundTheory».«GroupCoh».«augSES_obj_X₃» := P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661

attribute [defeq] P2M_GroundTheory_GroupCoh_augSES_obj_X__f61122e4f661
