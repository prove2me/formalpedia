-- Prove2me | Theorems.Thm_SCCThm8_Rig_gg_comm
-- name    : SCCThm8.Rig.gg_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:40.069219+00:00
-- url     : https://prove2.me/theorems/28444ee7-71d9-544e-aacb-5b9e0533a9e1
-- title:
--   Rig: gg comm
-- statement:
--   The Rig construction uses the gg comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L254-L265
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L254-L265

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
variable {G : Type*} [Group G] {k : ℕ}
variable {F : Finset (Fin (3 * k)) → G} {d : Fin (3 * k) → Fin (3 * k) → G} (hk : 2 ≤ k)
  (hs : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = d i j * F A)
include hk hs

theorem SCCThm8.Rig.gg_comm (o i j : Fin (3 * k)) : Commute (gg d o i) (gg d o j) := by sorry
