-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___augIdealRetract_82d7b9ae2009
-- name    : P2M_GroundTheory_GroupCoh___augIdealRetract_82d7b9ae2009
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:37:48.303053+00:00
-- url     : https://prove2.me/theorems/5562e02a-4ffd-4041-bc9a-f7d3404c1112
-- title:
--   P2 M Ground Theory Group Coh   aug Ideal Retract 82d7b9ae2009: P2 M Ground Theory Group Coh   aug Ideal Retract 82d7b9ae2009
-- statement:
--   The P2 M Ground Theory Group Coh   aug Ideal Retract 82d7b9ae2009 construction uses the P2 M Ground Theory Group Coh   aug Ideal Retract 82d7b9ae2009 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L82-L84

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

theorem P2M_GroundTheory_GroupCoh___augIdealRetract_82d7b9ae2009 (x : (Rep.leftRegular k G).V) :
    ((augIdealι k G).hom (augIdealRetract k G x)) =
      x - MonoidAlgebra.single 1 (augmentation k G x) := by sorry

alias «GroundTheory».«GroupCoh».«ι_augIdealRetract» := P2M_GroundTheory_GroupCoh___augIdealRetract_82d7b9ae2009
