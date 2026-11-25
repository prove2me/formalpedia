-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
-- name    : P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:20.118807+00:00
-- url     : https://prove2.me/theorems/6a98e515-ed56-4696-b737-de8c469476fb
-- title:
--   P2 M Ground Theory Group Coh aug SES obj X  d7360f095d2c: P2 M Ground Theory Group Coh aug SES obj X  d7360f095d2c
-- statement:
--   The P2 M Ground Theory Group Coh aug SES obj X  d7360f095d2c construction uses the P2 M Ground Theory Group Coh aug SES obj X  d7360f095d2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L299-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L299-L300

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

theorem P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c (X : Rep.{u} k G) :
    ((augSES k G).obj X).X₂ = Rep.leftRegular k G ⊗ X := by sorry

alias «GroundTheory».«GroupCoh».«augSES_obj_X₂» := P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c

attribute [defeq] P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
