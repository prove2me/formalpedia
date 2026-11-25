-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_pullbackSESHom____2eb40945c3eb
-- name    : P2M_GroundTheory_GroupCoh_pullbackSESHom____2eb40945c3eb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:58:00.439378+00:00
-- url     : https://prove2.me/theorems/d0669b54-4751-4487-8bb2-a894dfb21248
-- title:
--   P2 M Ground Theory Group Coh pullback SESHom    2eb40945c3eb: P2 M Ground Theory Group Coh pullback SESHom    2eb40945c3eb
-- statement:
--   The P2 M Ground Theory Group Coh pullback SESHom    2eb40945c3eb construction uses the P2 M Ground Theory Group Coh pullback SESHom    2eb40945c3eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PullbackExtension.lean#L109-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PullbackExtension.lean#L109-L109

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_PullbackExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (S : ShortComplex (Rep.{u} k G)) {Y : Rep.{u} k G} (β : Y ⟶ S.X₃)

theorem P2M_GroundTheory_GroupCoh_pullbackSESHom____2eb40945c3eb : (pullbackSESHom S β).τ₂ = pullbackFst S β := by sorry

alias «GroundTheory».«GroupCoh».«pullbackSESHom_τ₂» := P2M_GroundTheory_GroupCoh_pullbackSESHom____2eb40945c3eb

attribute [defeq] P2M_GroundTheory_GroupCoh_pullbackSESHom____2eb40945c3eb
