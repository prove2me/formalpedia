-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_pullbackSESHom____b79bf12ff0ad
-- name    : P2M_GroundTheory_GroupCoh_pullbackSESHom____b79bf12ff0ad
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:58:53.806361+00:00
-- url     : https://prove2.me/theorems/3ecd9f40-c9b1-442d-8d87-e403f0f0c85b
-- title:
--   P2 M Ground Theory Group Coh pullback SESHom    b79bf12ff0ad: P2 M Ground Theory Group Coh pullback SESHom    b79bf12ff0ad
-- statement:
--   The P2 M Ground Theory Group Coh pullback SESHom    b79bf12ff0ad construction uses the P2 M Ground Theory Group Coh pullback SESHom    b79bf12ff0ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PullbackExtension.lean#L108-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PullbackExtension.lean#L108-L108

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

theorem P2M_GroundTheory_GroupCoh_pullbackSESHom____b79bf12ff0ad : (pullbackSESHom S β).τ₁ = 𝟙 S.X₁ := by sorry

alias «GroundTheory».«GroupCoh».«pullbackSESHom_τ₁» := P2M_GroundTheory_GroupCoh_pullbackSESHom____b79bf12ff0ad

attribute [defeq] P2M_GroundTheory_GroupCoh_pullbackSESHom____b79bf12ff0ad
