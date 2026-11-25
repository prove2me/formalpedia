-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_iCocycles_cocyclesMap__90e7f21ea7a9
-- name    : P2M_GroundTheory_GroupCoh_iCocycles_cocyclesMap__90e7f21ea7a9
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:56.420583+00:00
-- url     : https://prove2.me/theorems/e3935993-c3c2-4bc7-b0f7-6c0e52992d31
-- title:
--   P2 M Ground Theory Group Coh i Cocycles cocycles Map  90e7f21ea7a9: P2 M Ground Theory Group Coh i Cocycles cocycles Map  90e7f21ea7a9
-- statement:
--   The P2 M Ground Theory Group Coh i Cocycles cocycles Map  90e7f21ea7a9 construction uses the P2 M Ground Theory Group Coh i Cocycles cocycles Map  90e7f21ea7a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupFunctorial.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupFunctorial.lean#L47-L52

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

theorem P2M_GroundTheory_GroupCoh_iCocycles_cocyclesMap__90e7f21ea7a9 {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B)
    (z : cocycles A n) :
    iCocycles B n (cocyclesMap f φ n z) = fun g => φ.hom (iCocycles A n z (f ∘ g)) := by sorry

alias «GroundTheory».«GroupCoh».«iCocycles_cocyclesMap'» := P2M_GroundTheory_GroupCoh_iCocycles_cocyclesMap__90e7f21ea7a9
