-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___apply_norm_cd75b4d7bf64
-- name    : P2M_GroundTheory_GroupCoh___apply_norm_cd75b4d7bf64
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:35.986216+00:00
-- url     : https://prove2.me/theorems/9243943b-c179-42a5-9ccd-1125f617a839
-- title:
--   P2 M Ground Theory Group Coh   apply norm cd75b4d7bf64: P2 M Ground Theory Group Coh   apply norm cd75b4d7bf64
-- statement:
--   The P2 M Ground Theory Group Coh   apply norm cd75b4d7bf64 construction uses the P2 M Ground Theory Group Coh   apply norm cd75b4d7bf64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DiagonalSuccIsoFreeInvSingle.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DiagonalSuccIsoFreeInvSingle.lean#L96-L99

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
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
open CategoryTheory Limits groupCohomology Rep
universe v w u
variable {k H : Type u} [CommRing k] [Group H] [Fintype H]

theorem P2M_GroundTheory_GroupCoh___apply_norm_cd75b4d7bf64 (B : Rep.{u} k H) (b : B) (s : H) : B.ρ s (B.ρ.norm b) = B.ρ.norm b := by sorry

alias «GroundTheory».«GroupCoh».«ρ_apply_norm» := P2M_GroundTheory_GroupCoh___apply_norm_cd75b4d7bf64
