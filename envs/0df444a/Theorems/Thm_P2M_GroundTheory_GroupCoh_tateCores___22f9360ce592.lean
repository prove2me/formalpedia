-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCores___22f9360ce592
-- name    : P2M_GroundTheory_GroupCoh_tateCores___22f9360ce592
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:55:22.559775+00:00
-- url     : https://prove2.me/theorems/d78e347b-68f4-481c-9199-a958db4fbf24
-- title:
--   P2 M Ground Theory Group Coh tate Cores   22f9360ce592: P2 M Ground Theory Group Coh tate Cores   22f9360ce592
-- statement:
--   The P2 M Ground Theory Group Coh tate Cores   22f9360ce592 construction uses the P2 M Ground Theory Group Coh tate Cores   22f9360ce592 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean#L99-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean#L99-L115

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
import Definitions.Def_GroundTheory_TateCohomology_ResCores
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
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

theorem P2M_GroundTheory_GroupCoh_tateCores___22f9360ce592 {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ (shortExact_map_resFunctor S hX) n ≫ (tateCores S (n + 1)).app X.X₁ =
      (tateCores S n).app X.X₃ ≫ TateCohomology.δ hX n := by sorry

alias «GroundTheory».«GroupCoh».«tateCores_δ» := P2M_GroundTheory_GroupCoh_tateCores___22f9360ce592
