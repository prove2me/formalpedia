-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- name    : P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:59.312803+00:00
-- url     : https://prove2.me/theorems/9d3e4746-3b98-4171-b0c7-310dd2695024
-- title:
--   P2 M Ground Theory Group Coh cup  apply a78771e4f336: P2 M Ground Theory Group Coh cup  apply a78771e4f336
-- statement:
--   The P2 M Ground Theory Group Coh cup  apply a78771e4f336 construction uses the P2 M Ground Theory Group Coh cup  apply a78771e4f336 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L248-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupCochains.lean#L248-L250

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
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
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}

theorem P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336 (h : p + q = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    cupₗ h f g = cupCochain h f g := by sorry

alias «GroundTheory».«GroupCoh».«cupₗ_apply» := P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336

attribute [defeq] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
