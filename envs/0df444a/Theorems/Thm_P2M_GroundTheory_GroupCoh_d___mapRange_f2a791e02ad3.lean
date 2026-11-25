-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_d___mapRange_f2a791e02ad3
-- name    : P2M_GroundTheory_GroupCoh_d___mapRange_f2a791e02ad3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:44.860879+00:00
-- url     : https://prove2.me/theorems/d58f5683-ba9d-462a-bed5-c92ad26b0d0b
-- title:
--   P2 M Ground Theory Group Coh d   map Range f2a791e02ad3: P2 M Ground Theory Group Coh d   map Range f2a791e02ad3
-- statement:
--   The P2 M Ground Theory Group Coh d   map Range f2a791e02ad3 construction uses the P2 M Ground Theory Group Coh d   map Range f2a791e02ad3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFree.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFree.lean#L18-L26

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

theorem P2M_GroundTheory_GroupCoh_d___mapRange_f2a791e02ad3 (y : G →₀ A) :
    d₁₀ B (Finsupp.mapRange.linearMap f.hom.toLinearMap y) = f.hom (d₁₀ A y) := by sorry

alias «GroundTheory».«GroupCoh».«d₁₀_mapRange» := P2M_GroundTheory_GroupCoh_d___mapRange_f2a791e02ad3
