-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_ComplementTruncationPencil_truncationResidual_natDegree_le_yukon_abec51854faa
-- name    : ProximityPrize.SubmissionUpper.ComplementTruncationPencil.truncationResidual_natDegree_le_yukon_abec51854faa
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-29T22:18:30.059991+00:00
-- url     : https://prove2.me/theorems/7446bfb8-75bf-4075-abd5-368b2e7dc56e
-- title:
--   ProximityPrize.SubmissionUpper.ComplementTruncationPencil.truncationResidual_natDegree_le
-- statement:
--   If the locator is monic of degree `A` and `E` is the residual tail below
--   `X^(s - 1)`, then the leading terms in the residual identity cancel.
--
--   Original contribution: dtumad, verified Better Codes submission 3cf4cb0e-7415-4347-9264-f1e9f9d8da9b. Source Lean 4.32.2, exact commit 20fb04406d24efa1ee911ff5c8694cbb5b206036. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/20fb04406d24efa1ee911ff5c8694cbb5b206036/ProximityPrize/SubmissionUpper/ComplementTruncationPencil.lean
--
--   p2m-history-complement:a3caa557a205a7ae7586799e1b006b5ba066b714b2ae4d76291b7ae898da5205
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1jb21wbGVtZW50OmEzY2FhNTU3YTIwNWE3YWU3NTg2Nzk5ZTFiMDA2YjViYTA2NmI3MTRiMmFlNGQ3NjI5MWI3YWU4OThkYTUyMDUiLCJoYXNoIjoiZTZhZTJkMTEzY2FlODQ4ODQ0Njk2Mjc1ZjU3NzcwNGQxNzk0YWNiZGNmOTk0MWY3MTZkNGY1ZWZhYTU1MGFiOCIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLkNvbXBsZW1lbnRUcnVuY2F0aW9uUGVuY2lsLnRydW5jYXRpb25SZXNpZHVhbF9uYXREZWdyZWVfbGVfeXVrb25fYWJlYzUxODU0ZmFhIiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoiYmV0dGVyLWNvZGVzLWhpc3RvcnkifQ]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




import Mathlib
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

/-- If the locator is monic of degree `A` and `E` is the residual tail below
`X^(s - 1)`, then the leading terms in the residual identity cancel. -/
theorem truncationResidual_natDegree_le_yukon_abec51854faa
    {A s : ℕ} {gamma : F} {L E : Polynomial F}
    (hs : 2 ≤ s) (hA : 1 ≤ A) (hLmonic : L.Monic)
    (hLdegree : L.natDegree = A) (hE : E.natDegree ≤ s - 2) :
    (Polynomial.X ^ (s - 1) * L - Polynomial.X ^ (A + s - 1) -
      Polynomial.C gamma * L * E - Polynomial.C gamma).natDegree ≤
        A + s - 2  := by sorry
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize
