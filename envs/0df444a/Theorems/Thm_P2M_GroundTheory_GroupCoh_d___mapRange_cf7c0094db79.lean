-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_d___mapRange_cf7c0094db79
-- name    : P2M_GroundTheory_GroupCoh_d___mapRange_cf7c0094db79
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:43.33874+00:00
-- url     : https://prove2.me/theorems/3d34f87d-78eb-496d-86db-c27e2be94e2c
-- title:
--   P2 M Ground Theory Group Coh d   map Range cf7c0094db79: P2 M Ground Theory Group Coh d   map Range cf7c0094db79
-- statement:
--   The P2 M Ground Theory Group Coh d   map Range cf7c0094db79 construction uses the P2 M Ground Theory Group Coh d   map Range cf7c0094db79 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFree.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFree.lean#L28-L40

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
import Definitions.Def_GroundTheory_TateCohomology_PGroupFree
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
open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (f : A ⟶ B)

theorem P2M_GroundTheory_GroupCoh_d___mapRange_cf7c0094db79 (c : G × G →₀ A) :
    d₂₁ B (Finsupp.mapRange.linearMap f.hom.toLinearMap c) =
      Finsupp.mapRange.linearMap f.hom.toLinearMap (d₂₁ A c) := by sorry

alias «GroundTheory».«GroupCoh».«d₂₁_mapRange» := P2M_GroundTheory_GroupCoh_d___mapRange_cf7c0094db79
