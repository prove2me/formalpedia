-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateAcyclic_res_indSES_X__55c5a5530310
-- name    : P2M_GroundTheory_GroupCoh_tateAcyclic_res_indSES_X__55c5a5530310
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:14.023706+00:00
-- url     : https://prove2.me/theorems/6ed1224d-f372-44ff-ad14-e558a1dd8ab2
-- title:
--   P2 M Ground Theory Group Coh tate Acyclic res ind SES X  55c5a5530310: P2 M Ground Theory Group Coh tate Acyclic res ind SES X  55c5a5530310
-- statement:
--   The P2 M Ground Theory Group Coh tate Acyclic res ind SES X  55c5a5530310 construction uses the P2 M Ground Theory Group Coh tate Acyclic res ind SES X  55c5a5530310 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateUnique.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateUnique.lean#L56-L58

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
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
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem P2M_GroundTheory_GroupCoh_tateAcyclic_res_indSES_X__55c5a5530310 (U : Subgroup G) [Fintype U] (A : Rep.{u} k G) :
    TateAcyclic ((resFunctor U.subtype).obj (indSES.obj A).X₂) := by sorry

alias «GroundTheory».«GroupCoh».«tateAcyclic_res_indSES_X₂» := P2M_GroundTheory_GroupCoh_tateAcyclic_res_indSES_X__55c5a5530310
