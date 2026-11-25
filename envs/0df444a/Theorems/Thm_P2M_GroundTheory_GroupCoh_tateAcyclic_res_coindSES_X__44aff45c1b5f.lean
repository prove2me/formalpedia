-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateAcyclic_res_coindSES_X__44aff45c1b5f
-- name    : P2M_GroundTheory_GroupCoh_tateAcyclic_res_coindSES_X__44aff45c1b5f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:37:46.447577+00:00
-- url     : https://prove2.me/theorems/5bd7939a-b1df-4f38-8710-86f3ec1eb806
-- title:
--   P2 M Ground Theory Group Coh tate Acyclic res coind SES X  44aff45c1b5f: P2 M Ground Theory Group Coh tate Acyclic res coind SES X  44aff45c1b5f
-- statement:
--   The P2 M Ground Theory Group Coh tate Acyclic res coind SES X  44aff45c1b5f construction uses the P2 M Ground Theory Group Coh tate Acyclic res coind SES X  44aff45c1b5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateUnique.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateUnique.lean#L52-L54

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

theorem P2M_GroundTheory_GroupCoh_tateAcyclic_res_coindSES_X__44aff45c1b5f (U : Subgroup G) [Fintype U] (A : Rep.{u} k G) :
    TateAcyclic ((resFunctor U.subtype).obj (coindSES.obj A).X₂) := by sorry

alias «GroundTheory».«GroupCoh».«tateAcyclic_res_coindSES_X₂» := P2M_GroundTheory_GroupCoh_tateAcyclic_res_coindSES_X__44aff45c1b5f
