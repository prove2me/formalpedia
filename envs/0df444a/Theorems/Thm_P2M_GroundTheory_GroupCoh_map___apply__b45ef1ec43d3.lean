-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_map___apply__b45ef1ec43d3
-- name    : P2M_GroundTheory_GroupCoh_map___apply__b45ef1ec43d3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:47.645783+00:00
-- url     : https://prove2.me/theorems/a37eb3c9-4f56-56dd-9203-64c9ea840701
-- title:
--   P2 M Ground Theory Group Coh map   apply  b45ef1ec43d3: P2 M Ground Theory Group Coh map   apply  b45ef1ec43d3
-- statement:
--   The P2 M Ground Theory Group Coh map   apply  b45ef1ec43d3 construction uses the P2 M Ground Theory Group Coh map   apply  b45ef1ec43d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupFunctorial.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupFunctorial.lean#L42-L45

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupFunctorial
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
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable (f : G →* H) {A₁ A₂ : Rep k H} {B₁ B₂ : Rep k G} {p q n : ℕ}

theorem P2M_GroundTheory_GroupCoh_map___apply__b45ef1ec43d3 {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B) (z : cocycles A n) :
    map f φ n (π A n z) = π B n (cocyclesMap f φ n z) := by sorry

alias «GroundTheory».«GroupCoh».«map_π_apply'» := P2M_GroundTheory_GroupCoh_map___apply__b45ef1ec43d3
