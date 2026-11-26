-- Prove2me | Theorems.Thm_P2M_BandParity_odd_subgroup_congruence__298617d94255
-- name    : P2M_BandParity_odd_subgroup_congruence__298617d94255
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:57:59.67758+00:00
-- url     : https://prove2.me/theorems/32f4c815-e73a-5de4-9015-098474fe3679
-- title:
--   P2 M Band Parity odd subgroup congruence  298617d94255: P2 M Band Parity odd subgroup congruence  298617d94255
-- statement:
--   **Theorem B (the odd-subgroup congruence).** For odd `N ≥ 3`, a subgroup `H` of `(ℤ/N)ˣ` of
--   odd order `h`, a coset `X = xH` and even `e ≥ 2`,
--   `T^{(e)}_{H,x}(N) ≡ h - 2 α(X) - 2 α(X^e) (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L252-L279
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L252-L279

module
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_OddSubgroup
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N]
variable (hN : Odd N) (hN3 : 3 ≤ N)
include hN hN3
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hH

theorem P2M_BandParity_odd_subgroup_congruence__298617d94255 (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e ≡
      (Nat.card H : ℤ) - 2 * oddCount (coset H x) - 2 * oddCount ((coset H x).image (· ^ e))
      [ZMOD 4] := by sorry

alias «BandParity».«odd_subgroup_congruence'» := P2M_BandParity_odd_subgroup_congruence__298617d94255
