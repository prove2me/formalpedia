-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_ComplementTruncationPencil_eval_neg_truncationQuotient_eq_monomialPencil_at_root_yukon_1c90e567e151
-- name    : ProximityPrize.SubmissionUpper.ComplementTruncationPencil.eval_neg_truncationQuotient_eq_monomialPencil_at_root_yukon_1c90e567e151
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-29T22:57:43.998581+00:00
-- url     : https://prove2.me/theorems/156f5c20-1b45-426c-a200-d3c496c43f94
-- title:
--   ProximityPrize.SubmissionUpper.ComplementTruncationPencil.eval_neg_truncationQuotient_eq_monomialPencil_at_root
-- statement:
--   Equivalently, the two polynomials agree at every root of `L`.
--
--   Original contribution: dtumad, verified Better Codes submission 3cf4cb0e-7415-4347-9264-f1e9f9d8da9b. Source Lean 4.32.2, exact commit 20fb04406d24efa1ee911ff5c8694cbb5b206036. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/20fb04406d24efa1ee911ff5c8694cbb5b206036/ProximityPrize/SubmissionUpper/ComplementTruncationPencil.lean
--
--   p2m-history-complement:e31082f416a73ec3c3c782dccd8e4ffbb8f547bdcdbed0b6d6b4fb422704ec48
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1jb21wbGVtZW50OmUzMTA4MmY0MTZhNzNlYzNjM2M3ODJkY2NkOGU0ZmZiYjhmNTQ3YmRjZGJlZDBiNmQ2YjRmYjQyMjcwNGVjNDgiLCJoYXNoIjoiN2MzNTgzY2Y5YjAyNTI3MjNhYWY0ZTQ5OGE0OTZhYTA2YzM2MGRlYmY2ZjQ4MzcxNmUyNmM4YWUyZDNmNDg2MyIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLkNvbXBsZW1lbnRUcnVuY2F0aW9uUGVuY2lsLmV2YWxfbmVnX3RydW5jYXRpb25RdW90aWVudF9lcV9tb25vbWlhbFBlbmNpbF9hdF9yb290X3l1a29uXzFjOTBlNTY3ZTE1MSIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImJldHRlci1jb2Rlcy1oaXN0b3J5In0]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




import Mathlib
import Definitions.Def_Yukon_c8e407f0f265709344b29f9b
import Definitions.Def_Yukon_fce1ab10c536c75cdaab6eaf
/-!
# Complement truncation and a monomial pencil

Let `L * R = X^N - 1`, and split the complementary factor as

`R = X^s * H + r * X^(s - 1) + E`.

If `gamma * r = -1`, multiplying the resulting quotient candidate by `X^s`
gives an expression involving only the locator `L` and the short residual
tail `E`.  At every root of `L`, the negative quotient evaluates as the
two-monomial pencil

`x^(A - 1) + gamma * x^(N - s)`.

This is the exact algebraic bridge behind the complement-truncation syndrome
experiment.  It deliberately does not assert that the residual high band can
be cancelled: at the current benchmark agreement it still has `8709`
coefficients.
-/

namespace ProximityPrize.SubmissionUpper.ComplementTruncationPencil

open Polynomial

variable {F : Type} [Field F]

/-- Equivalently, the two polynomials agree at every root of `L`. -/
theorem eval_neg_truncationQuotient_eq_monomialPencil_at_root_yukon_1c90e567e151
    {N A s : ℕ} {gamma x : F} {L H : Polynomial F}
    (hx : L.eval x = 0) :
    (-truncationQuotient N A s gamma L H).eval x =
      (monomialPencil N A s gamma).eval x  := by sorry
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize
