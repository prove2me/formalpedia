-- Prove2me | Theorems.Thm_SZ_Slice_exists_dB_ne
-- name    : SZ.Slice.exists_dB_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:02:37.027968+00:00
-- url     : https://prove2.me/theorems/da619ff3-9af8-4aa4-bd99-f58e209fabad
-- title:
--   Slice: exists d B ne
-- statement:
--   **L1(b).**  The `b`-digits are not eventually stuck at `0`: that would confine the
--   state to `L = [0, p√m)`, but one step from above `U` overshoots `m(U-p) ≥ p√m`, and below
--   `U` the state is merely multiplied by `m` forever.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L259-L326
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L259-L326

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.exists_dB_ne (he : S.e = (S.m : ℤ) - 1) (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ}
    (hk : 1 ≤ k₀) (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (N : ℕ) :
    ∃ k, N ≤ k ∧ S.dB (S.w0 j k₀) k ≠ 0 := by sorry
