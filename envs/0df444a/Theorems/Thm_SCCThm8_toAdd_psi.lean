-- Prove2me | Theorems.Thm_SCCThm8_toAdd_psi
-- name    : SCCThm8.toAdd_psi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:43.361845+00:00
-- url     : https://prove2.me/theorems/4898bd11-2f36-4e62-b8ca-a871e5c0eddf
-- title:
--   SCCThm8: to Add psi
-- statement:
--   In `Multiplicative ℤ`, `psi` is a linear form in the exponents.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Degeneration.lean#L29-L36
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Degeneration.lean#L29-L36

module
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.toAdd_psi {n : ℕ} (u : Fin n → Multiplicative ℤ) (e : Fin n → ℤ) :
    Multiplicative.toAdd (psi u e) = ∑ i, e i * Multiplicative.toAdd (u i) := by sorry
