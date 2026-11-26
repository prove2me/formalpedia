-- Prove2me | Theorems.Thm_P2M_BandParity_cosetBandSum_eq__5f1f29a5d302
-- name    : P2M_BandParity_cosetBandSum_eq__5f1f29a5d302
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:56.458864+00:00
-- url     : https://prove2.me/theorems/aaf6c9fd-1ce8-582f-b375-420e37d6eef7
-- title:
--   P2 M Band Parity coset Band Sum eq  5f1f29a5d302: P2 M Band Parity coset Band Sum eq  5f1f29a5d302
-- statement:
--   **Representative identity.** `T = ∑_{u ∈ xH} s(u) s(u^e)` for even `e ≥ 2`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L122-L163
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L122-L163

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

theorem P2M_BandParity_cosetBandSum_eq__5f1f29a5d302 (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e = ∑ u ∈ coset H x, uSign u * uSign (u ^ e) := by sorry

alias «BandParity».«cosetBandSum_eq'» := P2M_BandParity_cosetBandSum_eq__5f1f29a5d302
