-- Prove2me | Theorems.Thm_SZ_Slice_mem_MahlerZ_of_e_le
-- name    : SZ.Slice.mem_MahlerZ_of_e_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:06.407987+00:00
-- url     : https://prove2.me/theorems/51940f97-0d19-4c16-8f8d-93b3c746c692
-- title:
--   Slice: mem Mahler Z of e le
-- statement:
--   **The free case at `p = 2`.**  `e ≤ m - 2` — for `p = 2` exactly the even bases — needs
--   no hygiene, so the translate alone gives `√m ∈ 𝒵`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L748-L751
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L748-L751

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}

theorem SZ.Slice.mem_MahlerZ_of_e_le (S : Slice) (hp : S.p = 2) (he : S.e ≤ (S.m : ℤ) - 2) {j k₀ : ℤ}
    (hj : 1 ≤ j) (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    Real.sqrt S.m ∈ MahlerZ := by sorry
