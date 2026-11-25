-- Prove2me | Theorems.Thm_SCCThm8_psi_add
-- name    : SCCThm8.psi_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:09.245879+00:00
-- url     : https://prove2.me/theorems/d0d08f40-ea06-5fc4-a764-92c03befc81d
-- title:
--   SCCThm8: psi add
-- statement:
--   For a commuting family, `psi g` is additive.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L104-L110
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean#L104-L110

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.psi_add {G : Type*} [Group G] {n : ℕ} (g : Fin n → G)
    (hc : ∀ i j, Commute (g i) (g j)) (e e' : Fin n → ℤ) :
    psi g (e + e') = psi g e * psi g e' := by sorry
