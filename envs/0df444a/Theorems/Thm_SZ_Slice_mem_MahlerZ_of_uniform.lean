-- Prove2me | Theorems.Thm_SZ_Slice_mem_MahlerZ_of_uniform
-- name    : SZ.Slice.mem_MahlerZ_of_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:23:57.633308+00:00
-- url     : https://prove2.me/theorems/3e3e179d-2aa9-44f3-8fa2-e916a705b862
-- title:
--   Slice: mem Mahler Z of uniform
-- statement:
--   **Proposition 5.4 at `p = 2`.**  For `e = m - 1` and `m ≥ 5` the greedy's streams are
--   canonical, so `√m ∈ 𝒵`.  With `Slice.mem_MahlerZ_of_e_le` this covers every non-square
--   base.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L373-L377
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L373-L377

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.mem_MahlerZ_of_uniform (S : Slice) (hp : S.p = 2) (he : S.e = (S.m : ℤ) - 1)
    (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ} (hj : 1 ≤ j) (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    Real.sqrt S.m ∈ MahlerZ := by sorry
