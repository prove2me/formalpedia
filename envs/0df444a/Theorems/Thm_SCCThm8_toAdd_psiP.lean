-- Prove2me | Theorems.Thm_SCCThm8_toAdd_psiP
-- name    : SCCThm8.toAdd_psiP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:54:00.017343+00:00
-- url     : https://prove2.me/theorems/2fd38991-5c66-592a-9cd8-f90113aa7fcc
-- title:
--   SCCThm8: to Add psi P
-- statement:
--   In `Multiplicative ℤ`, `psiP` is a linear form in the exponents.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerDegeneration.lean#L33-L43
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerDegeneration.lean#L33-L43

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

theorem SCCThm8.toAdd_psiP {m n : ℕ} (u : Fin m → Fin n → Multiplicative ℤ) (e : Fin m → Fin n → ℤ) :
    Multiplicative.toAdd (psiP u e) = ∑ j, ∑ i, e j i * Multiplicative.toAdd (u j i) := by sorry
