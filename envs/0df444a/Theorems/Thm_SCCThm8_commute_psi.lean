-- Prove2me | Theorems.Thm_SCCThm8_commute_psi
-- name    : SCCThm8.commute_psi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:45.084195+00:00
-- url     : https://prove2.me/theorems/ac6e1d62-dd93-5adf-9857-e41e023a0abb
-- title:
--   SCCThm8: commute psi
-- statement:
--   An element commuting with every `g i` commutes with `psi g e`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerDegeneration.lean#L14-L18
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerDegeneration.lean#L14-L18

module
public import Definitions.Def_SCCThm8_PowerRigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.commute_psi {G : Type*} [Group G] {n : ℕ} {x : G} (g : Fin n → G)
    (h : ∀ i, Commute x (g i)) (e : Fin n → ℤ) : Commute x (psi g e) := by sorry
