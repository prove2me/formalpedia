-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
-- name    : P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:10:41.501511+00:00
-- url     : https://prove2.me/theorems/3fe164ce-7660-49c2-8d11-a1226e8ce236
-- title:
--   P2 M Ground Theory Group Coh ind SES map    b9067ca7808e: P2 M Ground Theory Group Coh ind SES map    b9067ca7808e
-- statement:
--   The P2 M Ground Theory Group Coh ind SES map    b9067ca7808e construction uses the P2 M Ground Theory Group Coh ind SES map    b9067ca7808e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DimensionShift.lean#L149-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DimensionShift.lean#L149-L149

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

theorem P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e {A B : Rep.{u} k G} (f : A ⟶ B) : (indSES.map f).τ₃ = f := by sorry

alias «GroundTheory».«GroupCoh».«indSES_map_τ₃» := P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e

attribute [defeq] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
