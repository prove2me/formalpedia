-- Prove2me | Theorems.Thm_P2M_BandParity_odd_t__8898b1b7a17c
-- name    : P2M_BandParity_odd_t__8898b1b7a17c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:56:01.053851+00:00
-- url     : https://prove2.me/theorems/793a96b9-2b44-49ac-b91a-0cc193562d06
-- title:
--   P2 M Band Parity odd t  8898b1b7a17c: P2 M Band Parity odd t  8898b1b7a17c
-- statement:
--   **Proposition 3.2 (oddness of `t`).**
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L208-L214
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L208-L214

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem P2M_BandParity_odd_t__8898b1b7a17c (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (t χ) := by sorry

alias «BandParity».«odd_t'» := P2M_BandParity_odd_t__8898b1b7a17c
