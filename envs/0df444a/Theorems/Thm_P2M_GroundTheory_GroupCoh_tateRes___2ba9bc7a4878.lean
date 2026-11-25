-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateRes___2ba9bc7a4878
-- name    : P2M_GroundTheory_GroupCoh_tateRes___2ba9bc7a4878
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:36.037177+00:00
-- url     : https://prove2.me/theorems/3242b16a-3433-500f-abc2-b5450416d1cc
-- title:
--   P2 M Ground Theory Group Coh tate Res   2ba9bc7a4878: P2 M Ground Theory Group Coh tate Res   2ba9bc7a4878
-- statement:
--   The P2 M Ground Theory Group Coh tate Res   2ba9bc7a4878 construction uses the P2 M Ground Theory Group Coh tate Res   2ba9bc7a4878 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean#L51-L61

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

theorem P2M_GroundTheory_GroupCoh_tateRes___2ba9bc7a4878 {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateRes S (n + 1)).app X.X₁ =
      (tateRes S n).app X.X₃ ≫ TateCohomology.δ (shortExact_map_resFunctor S hX) n := by sorry

alias «GroundTheory».«GroupCoh».«tateRes_δ» := P2M_GroundTheory_GroupCoh_tateRes___2ba9bc7a4878
