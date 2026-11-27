-- Prove2me | Theorems.Thm_RamanujanNested_altSum_shift_ge_one
-- name    : RamanujanNested.altSum_shift_ge_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:02:00.311092+00:00
-- url     : https://prove2.me/theorems/89855853-2173-543d-aacb-c37dc7dd1975
-- title:
--   Ramanujan Nested: alt Sum shift ge one
-- statement:
--   **The invariant that makes the seed `T = 1` (not `0`) the right canonical
--   seed for this signed family.** `(-1)^n + altSum n x ≥ 1` for `x ≥ 2`: trivial
--   for even `n` (reduces to `altSum n x ≥ 0`); for odd `n` (`n ≥ 3`) needs
--   `altSum n x ≥ 2`, which follows from `x^n ≥ x^3 ≥ 2x+1`. This is exactly why
--   the odd-`n` forward evaluation from seed `0` fails numerically but seed `1`
--   (or any seed `≥ 1`) works: the radicand would go negative starting from `0`.
--
--   Source: https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/IdentityChainNthRoot.lean#L143-L168
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/IdentityChainNthRoot.lean#L143-L168

module
public import Mathlib
public import Definitions.Def_RamanujanNested_IdentityChainNthRoot
set_option autoImplicit true
@[expose] public section
open RamanujanNested
open Finset

theorem RamanujanNested.altSum_shift_ge_one {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 2 ≤ x) :
    (1 : ℝ) ≤ (-1 : ℝ) ^ n + altSum n x := by sorry
