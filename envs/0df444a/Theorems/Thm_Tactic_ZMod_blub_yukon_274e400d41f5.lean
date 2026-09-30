-- Prove2me | Theorems.Thm_Tactic_ZMod_blub_yukon_274e400d41f5
-- name    : Tactic.ZMod.blub_yukon_274e400d41f5
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T03:59:49.330453+00:00
-- url     : https://prove2.me/theorems/bfe363b1-2396-4550-b947-009f5380bba2
-- title:
--   Tactic.ZMod.blub
-- statement:
--   Source declaration Tactic.ZMod.blub.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/PrattCertificate.lean
--
--   yukon-proof-operation:3b9083b5-c687-413f-b678-88ec38970c3d; Yukon contributor: historical-source-bootstrap
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246M2I5MDgzYjUtYzY4Ny00MTNmLWI2NzgtODhlYzM4OTcwYzNkOyBZdWtvbiBjb250cmlidXRvcjogaGlzdG9yaWNhbC1zb3VyY2UtYm9vdHN0cmFwIiwiaGFzaCI6ImE3N2FhN2JhZGNjOGU4ZDA4MDAxOTczMmUwNjhmNDA3ZWRmOGIxZjMxMjI2MTYzOTI4NjUyM2M5ZTBkNzE3MzgiLCJraW5kIjoicHJvYmxlbSIsInRhcmdldCI6IlRhY3RpYy5aTW9kLmJsdWJfeXVrb25fMjc0ZTQwMGQ0MWY1IiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoiYmV0dGVyLWNvZGVzLWhpc3RvcnkifQ]

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
-- return q(sorry)
  -- have npred : Q(ℕ) := mkRawNatLit (n.natLit! - 1)
  -- haveI : $n =Q Nat.succ $npred := ⟨⟩
  -- -- haveI : $npred =Q $n - 1 := ⟨⟩
  -- let ⟨c, pc⟩ := evalNatPowMod a' npred n
  -- let pc' : Q(Nat.mod (Nat.pow «$a'» «$npred») «$n» = «$c») := q(sorry)
  -- -- have hc : Q(decide ($c = 1) = true) := (q(Eq.refl true) : Expr)
  -- haveI : $c =Q 1 := ⟨⟩
  -- -- return q(sorry)
  -- return q(ZMod.powEqOfPowMod $a $ha $pc' (.refl _))

theorem ZMod.blub_yukon_274e400d41f5 :
    ∀ {n q c : ℕ} (a : ZMod n), (decide (n ≥ 2) = true) → (decide (c < n) = true) →
      (decide (c ≠ 1) = true) → IsNat (a ^ ((n - 1) / q)) c → a ^ ((n - 1) / q) ≠ 1
   := by sorry
end Tactic
end
end
