-- Prove2me | Theorems.Thm_SCCThm8_psiP_add
-- name    : SCCThm8.psiP_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:54:09.869097+00:00
-- url     : https://prove2.me/theorems/a33a12cf-5ce3-483d-a8ed-db83b34755f3
-- title:
--   SCCThm8: psi P add
-- statement:
--   For a commuting family, `psiP g` is additive.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerDegeneration.lean#L21-L30
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerDegeneration.lean#L21-L30

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

theorem SCCThm8.psiP_add {G : Type*} [Group G] {m n : ℕ} (g : Fin m → Fin n → G)
    (hc : ∀ j i j' i', Commute (g j i) (g j' i')) (e e' : Fin m → Fin n → ℤ) :
    psiP g (e + e') = psiP g e * psiP g e' := by sorry
