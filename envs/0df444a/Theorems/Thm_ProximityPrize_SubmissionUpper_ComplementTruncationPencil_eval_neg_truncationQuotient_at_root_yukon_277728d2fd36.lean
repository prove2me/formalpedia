-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_ComplementTruncationPencil_eval_neg_truncationQuotient_at_root_yukon_277728d2fd36
-- name    : ProximityPrize.SubmissionUpper.ComplementTruncationPencil.eval_neg_truncationQuotient_at_root_yukon_277728d2fd36
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-29T22:28:09.882992+00:00
-- url     : https://prove2.me/theorems/edba1f45-90e1-4119-8800-f5c38c88fd29
-- title:
--   ProximityPrize.SubmissionUpper.ComplementTruncationPencil.eval_neg_truncationQuotient_at_root
-- statement:
--   At a root of the locator, the negative truncation quotient evaluates to
--   the corresponding two-monomial pencil value.
--
--   Original contribution: dtumad, verified Better Codes submission 3cf4cb0e-7415-4347-9264-f1e9f9d8da9b. Source Lean 4.32.2, exact commit 20fb04406d24efa1ee911ff5c8694cbb5b206036. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/20fb04406d24efa1ee911ff5c8694cbb5b206036/ProximityPrize/SubmissionUpper/ComplementTruncationPencil.lean
--
--   p2m-history-complement:1af202e5460d53700a3597ffb2bc4ffb0ff495a2087f76dd07a944e090c281ad
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1jb21wbGVtZW50OjFhZjIwMmU1NDYwZDUzNzAwYTM1OTdmZmIyYmM0ZmZiMGZmNDk1YTIwODdmNzZkZDA3YTk0NGUwOTBjMjgxYWQiLCJoYXNoIjoiMjAzMjUyNjc2ZjZhMGMyYWFjYmI1NDQwMzJjYWUxN2Q1ZDgwNWQzMDI2M2IzMjg0MzUyZTI2Zjk0YjA5MDA2NiIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLkNvbXBsZW1lbnRUcnVuY2F0aW9uUGVuY2lsLmV2YWxfbmVnX3RydW5jYXRpb25RdW90aWVudF9hdF9yb290X3l1a29uXzI3NzcyOGQyZmQzNiIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImJldHRlci1jb2Rlcy1oaXN0b3J5In0]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




import Mathlib
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

/-- At a root of the locator, the negative truncation quotient evaluates to
the corresponding two-monomial pencil value. -/
theorem eval_neg_truncationQuotient_at_root_yukon_277728d2fd36
    {N A s : ℕ} {gamma x : F} {L H : Polynomial F}
    (hx : L.eval x = 0) :
    (-truncationQuotient N A s gamma L H).eval x =
      x ^ (A - 1) + gamma * x ^ (N - s)  := by sorry
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize
