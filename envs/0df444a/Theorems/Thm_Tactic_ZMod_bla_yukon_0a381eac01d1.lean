-- Prove2me | Theorems.Thm_Tactic_ZMod_bla_yukon_0a381eac01d1
-- name    : Tactic.ZMod.bla_yukon_0a381eac01d1
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T03:45:50.133018+00:00
-- url     : https://prove2.me/theorems/1beebdf7-fbe4-454d-a833-728e38159365
-- title:
--   Tactic.ZMod.bla
-- statement:
--   Source declaration Tactic.ZMod.bla.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/PrattCertificate.lean
--
--   yukon-proof-operation:0ec87eb1-43b5-4143-b985-eabde76823d6; Yukon contributor: historical-source-bootstrap
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MGVjODdlYjEtNDNiNS00MTQzLWI5ODUtZWFiZGU3NjgyM2Q2OyBZdWtvbiBjb250cmlidXRvcjogaGlzdG9yaWNhbC1zb3VyY2UtYm9vdHN0cmFwIiwiaGFzaCI6ImNjNzI1MjRhNDE2ZThhMDA2M2QzMWNhOGY2OGVkNmQ1OGMxYTNlNWY0ZDU3NmRlYzQ4Zjc1NDgxYWRhZTY2ZDIiLCJraW5kIjoicHJvYmxlbSIsInRhcmdldCI6IlRhY3RpYy5aTW9kLmJsYV95dWtvbl8wYTM4MWVhYzAxZDEiLCJlbnZpcm9ubWVudCI6eyJ0b29sY2hhaW4iOiJsZWFucHJvdmVyL2xlYW40OnY0LjMzLjEiLCJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCJ9LCJ0YWciOiJiZXR0ZXItY29kZXMtaGlzdG9yeSJ9]

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality


@[expose] public section
/-!
# The Lucas test for primes.

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO

- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness.
  Use `Units.IsCyclic` from `RingTheory/IntegralDomain` to show the group is cyclic.
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate Pratt primality certificates into the norm_num primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`: In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/

@[expose] public section

section New

-- TODO: port to `Mathlib`?
end New
-- cannot do ^1 correctly it seems?
-- theorem prime_987654319 : Nat.Prime 987654319 := sorry
namespace Tactic

open Lean Meta Simp
open Lean.Elab
open Tactic
open Qq
open Mathlib.Meta.NormNum

theorem ZMod.bla_yukon_0a381eac01d1 : ∀ {n c : ℕ} (a : ZMod n), c = 1 → IsNat (a ^ (n - 1)) c → a ^ (n - 1) = 1
   := by sorry
end Tactic
end
end
