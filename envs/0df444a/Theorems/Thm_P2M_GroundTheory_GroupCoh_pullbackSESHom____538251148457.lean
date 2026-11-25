-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_pullbackSESHom____538251148457
-- name    : P2M_GroundTheory_GroupCoh_pullbackSESHom____538251148457
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:28.419517+00:00
-- url     : https://prove2.me/theorems/76a45bac-d50c-417d-9217-ca90cd2994e5
-- title:
--   P2 M Ground Theory Group Coh pullback SESHom    538251148457: P2 M Ground Theory Group Coh pullback SESHom    538251148457
-- statement:
--   The P2 M Ground Theory Group Coh pullback SESHom    538251148457 construction uses the P2 M Ground Theory Group Coh pullback SESHom    538251148457 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PullbackExtension.lean#L110-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PullbackExtension.lean#L110-L110

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

theorem P2M_GroundTheory_GroupCoh_pullbackSESHom____538251148457 : (pullbackSESHom S β).τ₃ = β := by sorry

alias «GroundTheory».«GroupCoh».«pullbackSESHom_τ₃» := P2M_GroundTheory_GroupCoh_pullbackSESHom____538251148457

attribute [defeq] P2M_GroundTheory_GroupCoh_pullbackSESHom____538251148457
