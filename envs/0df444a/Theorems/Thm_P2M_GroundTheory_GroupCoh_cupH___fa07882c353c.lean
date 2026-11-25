-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_cupH___fa07882c353c
-- name    : P2M_GroundTheory_GroupCoh_cupH___fa07882c353c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:23.829918+00:00
-- url     : https://prove2.me/theorems/5a1fad42-a86f-4d89-942f-99cbb9a79760
-- title:
--   P2 M Ground Theory Group Coh cup H   fa07882c353c: P2 M Ground Theory Group Coh cup H   fa07882c353c
-- statement:
--   The P2 M Ground Theory Group Coh cup H   fa07882c353c construction uses the P2 M Ground Theory Group Coh cup H   fa07882c353c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupProduct.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupProduct.lean#L151-L154

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

theorem P2M_GroundTheory_GroupCoh_cupH___fa07882c353c (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    cupH h (π A p z) (π B q w) = π (A ⊗ B) n (cupCocycles h z w) := by sorry

alias «GroundTheory».«GroupCoh».«cupH_π» := P2M_GroundTheory_GroupCoh_cupH___fa07882c353c
