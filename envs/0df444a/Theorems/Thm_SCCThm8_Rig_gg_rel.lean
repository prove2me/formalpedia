-- Prove2me | Theorems.Thm_SCCThm8_Rig_gg_rel
-- name    : SCCThm8.Rig.gg_rel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:20.143736+00:00
-- url     : https://prove2.me/theorems/c41c671f-16f2-5376-aee2-be237d510a91
-- title:
--   Rig: gg rel
-- statement:
--   The Rig construction uses the gg rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L243-L252
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L243-L252

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

theorem SCCThm8.Rig.gg_rel (o : Fin (3 * k)) {i j : Fin (3 * k)} (hij : i ≠ j) :
    d i j = gg d o j * (gg d o i)⁻¹ := by sorry
