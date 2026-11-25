-- Prove2me | Theorems.Thm_P2M_SZ_Slice_digitReal_compl__fb997b0ac62f
-- name    : P2M_SZ_Slice_digitReal_compl__fb997b0ac62f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:55:46.110801+00:00
-- url     : https://prove2.me/theorems/84409d27-5305-5acd-9a51-b20375e36f6d
-- title:
--   P2 M SZ Slice digit Real compl  fb997b0ac62f: P2 M SZ Slice digit Real compl  fb997b0ac62f
-- statement:
--   **`M - K = K`.**  The digitwise complement `d ↦ e - d` realises `M - ⟨d⟩`, where
--   `M = e/(m-1)` is the maximum of the restricted-digit Cantor set.  At `e = m - 1` this is
--   `SZ.digitReal_compl`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L521-L554
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L521-L554

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

theorem P2M_SZ_Slice_digitReal_compl__fb997b0ac62f (S : Slice) {d : ℕ → ℤ} (h : IsDigits S.m d) (hd : ∀ i, d i ≤ S.e) :
    digitReal S.m (fun i => S.e - d i) = S.M - digitReal S.m d := by sorry

alias «SZ».«Slice».«digitReal_compl'» := P2M_SZ_Slice_digitReal_compl__fb997b0ac62f
