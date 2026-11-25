-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
-- name    : P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:10.389237+00:00
-- url     : https://prove2.me/theorems/f0952fb8-5882-49da-a286-452ea99dfe0b
-- title:
--   P2 M Ground Theory Group Coh ind SES obj X  c57492aa2d98: P2 M Ground Theory Group Coh ind SES obj X  c57492aa2d98
-- statement:
--   The P2 M Ground Theory Group Coh ind SES obj X  c57492aa2d98 construction uses the P2 M Ground Theory Group Coh ind SES obj X  c57492aa2d98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DimensionShift.lean#L145-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DimensionShift.lean#L145-L145

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

theorem P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98 (A : Rep.{u} k G) : (indSES.obj A).X₃ = A := by sorry

alias «GroundTheory».«GroupCoh».«indSES_obj_X₃» := P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98

attribute [defeq] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
