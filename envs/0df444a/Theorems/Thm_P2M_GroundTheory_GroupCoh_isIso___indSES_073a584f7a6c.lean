-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_isIso___indSES_073a584f7a6c
-- name    : P2M_GroundTheory_GroupCoh_isIso___indSES_073a584f7a6c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:13:23.351444+00:00
-- url     : https://prove2.me/theorems/d4fee60e-cbf9-4aef-8cbd-8f8ab8e65a1a
-- title:
--   P2 M Ground Theory Group Coh is Iso   ind SES 073a584f7a6c: P2 M Ground Theory Group Coh is Iso   ind SES 073a584f7a6c
-- statement:
--   The P2 M Ground Theory Group Coh is Iso   ind SES 073a584f7a6c construction uses the P2 M Ground Theory Group Coh is Iso   ind SES 073a584f7a6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DimensionShift.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DimensionShift.lean#L168-L170

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
variable [Fintype G]

theorem P2M_GroundTheory_GroupCoh_isIso___indSES_073a584f7a6c (A : Rep.{u} k G) (n : ℤ) :
    IsIso (TateCohomology.δ (indSES_shortExact A) n) := by sorry

alias «GroundTheory».«GroupCoh».«isIso_δ_indSES» := P2M_GroundTheory_GroupCoh_isIso___indSES_073a584f7a6c
