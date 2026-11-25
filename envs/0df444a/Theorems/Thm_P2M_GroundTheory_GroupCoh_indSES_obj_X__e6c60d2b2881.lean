-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- name    : P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:13.585376+00:00
-- url     : https://prove2.me/theorems/d31daa86-ef34-41a9-beb7-e82dc80c3003
-- title:
--   P2 M Ground Theory Group Coh ind SES obj X  e6c60d2b2881: P2 M Ground Theory Group Coh ind SES obj X  e6c60d2b2881
-- statement:
--   The P2 M Ground Theory Group Coh ind SES obj X  e6c60d2b2881 construction uses the P2 M Ground Theory Group Coh ind SES obj X  e6c60d2b2881 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DimensionShift.lean#L142-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DimensionShift.lean#L142-L143

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]

theorem P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881 (A : Rep.{u} k G) :
    (indSES.obj A).X₂ = ind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) := by sorry

alias «GroundTheory».«GroupCoh».«indSES_obj_X₂» := P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881

attribute [defeq] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
