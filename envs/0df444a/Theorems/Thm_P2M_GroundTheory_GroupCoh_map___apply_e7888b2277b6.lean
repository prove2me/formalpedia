-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_map___apply_e7888b2277b6
-- name    : P2M_GroundTheory_GroupCoh_map___apply_e7888b2277b6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:04.031633+00:00
-- url     : https://prove2.me/theorems/f22d1d7a-d647-4793-97a3-75792e5c04a7
-- title:
--   P2 M Ground Theory Group Coh map   apply e7888b2277b6: P2 M Ground Theory Group Coh map   apply e7888b2277b6
-- statement:
--   The P2 M Ground Theory Group Coh map   apply e7888b2277b6 construction uses the P2 M Ground Theory Group Coh map   apply e7888b2277b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupProduct.lean#L167-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupProduct.lean#L167-L171

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}

theorem P2M_GroundTheory_GroupCoh_map___apply_e7888b2277b6 {A' : Rep k G} (φ : A ⟶ A') (z : cocycles A n) :
    map (MonoidHom.id G) φ n (π A n z) = π A' n (cocyclesMap (MonoidHom.id G) φ n z) := by sorry

alias «GroundTheory».«GroupCoh».«map_π_apply» := P2M_GroundTheory_GroupCoh_map___apply_e7888b2277b6
