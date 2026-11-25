-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateAcyclic_augSES_tensorRight_X__2ee3f5d8edb9
-- name    : P2M_GroundTheory_GroupCoh_tateAcyclic_augSES_tensorRight_X__2ee3f5d8edb9
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:37:39.589461+00:00
-- url     : https://prove2.me/theorems/791c289b-cc47-4e68-b6a0-7a6b3918f370
-- title:
--   P2 M Ground Theory Group Coh tate Acyclic aug SES tensor Right X  2ee3f5d8edb9: P2 M Ground Theory Group Coh tate Acyclic aug SES tensor Right X  2ee3f5d8edb9
-- statement:
--   The P2 M Ground Theory Group Coh tate Acyclic aug SES tensor Right X  2ee3f5d8edb9 construction uses the P2 M Ground Theory Group Coh tate Acyclic aug SES tensor Right X  2ee3f5d8edb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L348-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L348-L350

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
variable [Fintype G]

theorem P2M_GroundTheory_GroupCoh_tateAcyclic_augSES_tensorRight_X__2ee3f5d8edb9 (A B : Rep.{u} k G) :
    TateAcyclic (((augSES k G).obj A).map (tensorRight B)).X₂ := by sorry

alias «GroundTheory».«GroupCoh».«tateAcyclic_augSES_tensorRight_X₂» := P2M_GroundTheory_GroupCoh_tateAcyclic_augSES_tensorRight_X__2ee3f5d8edb9
