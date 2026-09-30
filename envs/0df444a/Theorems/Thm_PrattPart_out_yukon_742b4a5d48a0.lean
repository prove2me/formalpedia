-- Prove2me | Theorems.Thm_PrattPart_out_yukon_742b4a5d48a0
-- name    : PrattPart.out_yukon_742b4a5d48a0
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T01:01:23.678251+00:00
-- url     : https://prove2.me/theorems/033df896-c858-42ee-b15f-d17ae4c2e960
-- title:
--   PrattPart.out
-- statement:
--   Source declaration PrattPart.out.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/PrattCertificate.lean
--
--   yukon-proof-operation:90eadd14-d6ad-47f9-98e8-f47a39d3144f; Yukon contributor: historical-source-bootstrap
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OTBlYWRkMTQtZDZhZC00N2Y5LTk4ZTgtZjQ3YTM5ZDMxNDRmOyBZdWtvbiBjb250cmlidXRvcjogaGlzdG9yaWNhbC1zb3VyY2UtYm9vdHN0cmFwIiwiaGFzaCI6ImEzNGVkYjE2MTdkMzE1N2U0YzNmNzBjZjUzZjgwMTQwMGM4OTI3MDAxYjEyZDVmNGEyMmU1MDQ0YmI1Y2E0NDYiLCJraW5kIjoicHJvYmxlbSIsInRhcmdldCI6IlByYXR0UGFydC5vdXRfeXVrb25fNzQyYjRhNWQ0OGEwIiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoiYmV0dGVyLWNvZGVzLWhpc3RvcnkifQ]

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality


public import Definitions.Def_Yukon_5a1c8f8f8be9100f7eedfb21
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

theorem PrattPart.out_yukon_742b4a5d48a0 {p : ℕ} {a : ZMod p} {n : ℕ} (h : PrattPart p a n) :
    ∀ q : ℕ, q.Prime → q ∣ n → a ^ ((p - 1) / q) ≠ 1  := by sorry
end
end
