-- Prove2me | Theorems.Thm_P2M_BandParity_T_eq__1be22a5fd3a8
-- name    : P2M_BandParity_T_eq__1be22a5fd3a8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:49.185678+00:00
-- url     : https://prove2.me/theorems/52cafc28-9616-43af-9d90-1e2b413e2b37
-- title:
--   P2 M Band Parity T eq  1be22a5fd3a8: P2 M Band Parity T eq  1be22a5fd3a8
-- statement:
--   **Proposition 3.1 (the value).** `∑ χ(n) n = p (k + i t)`, i.e. `B₁,χ = k + i t`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L185-L196
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L185-L196

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

theorem P2M_BandParity_T_eq__1be22a5fd3a8 (hp5 : 5 < p) : T χ = (p : GaussianInt) * ((k χ : GaussianInt) + gi * (t χ)) := by sorry

alias «BandParity».«T_eq'» := P2M_BandParity_T_eq__1be22a5fd3a8
