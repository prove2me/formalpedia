-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_ComplementTruncationPencil_X_pow_mul_truncationQuotient_yukon_111c1eb01369
-- name    : ProximityPrize.SubmissionUpper.ComplementTruncationPencil.X_pow_mul_truncationQuotient_yukon_111c1eb01369
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-29T22:28:20.28586+00:00
-- url     : https://prove2.me/theorems/8309f95a-0c01-479f-99c8-88c6066296e3
-- title:
--   ProximityPrize.SubmissionUpper.ComplementTruncationPencil.X_pow_mul_truncationQuotient
-- statement:
--   The complement-truncation identity.  The hypotheses `s ≤ N` and
--   `1 ≤ A` are exactly what is needed to recombine the truncated exponents.
--
--   Original contribution: dtumad, verified Better Codes submission 3cf4cb0e-7415-4347-9264-f1e9f9d8da9b. Source Lean 4.32.2, exact commit 20fb04406d24efa1ee911ff5c8694cbb5b206036. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/20fb04406d24efa1ee911ff5c8694cbb5b206036/ProximityPrize/SubmissionUpper/ComplementTruncationPencil.lean
--
--   p2m-history-complement:f58ed1109029209290b8c915502abda6fb64313fd77883c2604b8169c0dcf7bf
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1jb21wbGVtZW50OmY1OGVkMTEwOTAyOTIwOTI5MGI4YzkxNTUwMmFiZGE2ZmI2NDMxM2ZkNzc4ODNjMjYwNGI4MTY5YzBkY2Y3YmYiLCJoYXNoIjoiZmNkNzdlOTE4YjZkMTYxMjk3NjYwOGFhZTZjNzM5NjZiNDQ4NDI1NzNmN2Y1OGFjMTFlMDY2MzUxYWYxYjE5ZCIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLkNvbXBsZW1lbnRUcnVuY2F0aW9uUGVuY2lsLlhfcG93X211bF90cnVuY2F0aW9uUXVvdGllbnRfeXVrb25fMTExYzFlYjAxMzY5IiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoiYmV0dGVyLWNvZGVzLWhpc3RvcnkifQ]

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

/-- The complement-truncation identity.  The hypotheses `s ≤ N` and
`1 ≤ A` are exactly what is needed to recombine the truncated exponents. -/
theorem X_pow_mul_truncationQuotient_yukon_111c1eb01369
    {N A s : ℕ} {gamma r : F} {L R H E : Polynomial F}
    (hsN : s ≤ N) (hA : 1 ≤ A)
    (hgrid : L * R = Polynomial.X ^ N - 1)
    (htrunc : R = Polynomial.X ^ s * H +
      Polynomial.C r * Polynomial.X ^ (s - 1) + E)
    (hgamma : gamma * r = -1) :
    Polynomial.X ^ s * truncationQuotient N A s gamma L H =
      Polynomial.X ^ (s - 1) * L - Polynomial.X ^ (A + s - 1) -
        Polynomial.C gamma * L * E - Polynomial.C gamma  := by sorry
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize
