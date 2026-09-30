-- Prove2me | Theorems.Thm_PrattCertificate_out_yukon_b1abd2ed34d1
-- name    : PrattCertificate.out_yukon_b1abd2ed34d1
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T01:20:08.849649+00:00
-- url     : https://prove2.me/theorems/9f68863f-6f02-4ed2-b297-28eb6b246078
-- title:
--   PrattCertificate.out
-- statement:
--   Source declaration PrattCertificate.out.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/PrattCertificate.lean
--
--   yukon-proof-operation:2ab7d305-e569-418a-bd4e-0763d54b1e71; Yukon contributor: historical-source-bootstrap
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MmFiN2QzMDUtZTU2OS00MThhLWJkNGUtMDc2M2Q1NGIxZTcxOyBZdWtvbiBjb250cmlidXRvcjogaGlzdG9yaWNhbC1zb3VyY2UtYm9vdHN0cmFwIiwiaGFzaCI6IjRmNDQ3ZmE0YWZhMTMzMjVmZWViZWU1NTM1MGZhNzM2ZjViNGY5ZmFmZjg4OGI0ZGEzMDFjZTIwMjlkNTc2NzYiLCJraW5kIjoicHJvYmxlbSIsInRhcmdldCI6IlByYXR0Q2VydGlmaWNhdGUub3V0X3l1a29uX2IxYWJkMmVkMzRkMSIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImJldHRlci1jb2Rlcy1oaXN0b3J5In0]

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality


public import Definitions.Def_Yukon_92052b9f6262f4f17145e198
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

theorem PrattCertificate.out_yukon_b1abd2ed34d1 {p : ℕ} (c : PrattCertificate p) : p.Prime  := by sorry
end
end
