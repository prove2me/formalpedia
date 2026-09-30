-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionUpper_ComplementTruncationPencil_truncationQuotient_natDegree_le_yukon_b6a1dced94ac
-- name    : ProximityPrize.SubmissionUpper.ComplementTruncationPencil.truncationQuotient_natDegree_le_yukon_b6a1dced94ac
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-29T22:57:34.017058+00:00
-- url     : https://prove2.me/theorems/dfaf68e9-a1cb-43bd-86ef-216144107dd2
-- title:
--   ProximityPrize.SubmissionUpper.ComplementTruncationPencil.truncationQuotient_natDegree_le
-- statement:
--   Multiplication by `X^s` transfers a degree bound on the residual side of
--   the identity back to the quotient.
--
--   Original contribution: dtumad, verified Better Codes submission 3cf4cb0e-7415-4347-9264-f1e9f9d8da9b. Source Lean 4.32.2, exact commit 20fb04406d24efa1ee911ff5c8694cbb5b206036. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/20fb04406d24efa1ee911ff5c8694cbb5b206036/ProximityPrize/SubmissionUpper/ComplementTruncationPencil.lean
--
--   p2m-history-complement:1ee73d95bd5a1e25e5707003e7670cdf3e403219dc61c4e3ed190e0268c716a0
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1jb21wbGVtZW50OjFlZTczZDk1YmQ1YTFlMjVlNTcwNzAwM2U3NjcwY2RmM2U0MDMyMTlkYzYxYzRlM2VkMTkwZTAyNjhjNzE2YTAiLCJoYXNoIjoiYzJhZjI2ZTk3OTZmMThmZDdiNzBlYTFhMTFkMmNjZDY4NjY3ZGI0NjIzNTlmYjA1MDc1OWMxZDBmNzRkZTNjMiIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemUuU3VibWlzc2lvblVwcGVyLkNvbXBsZW1lbnRUcnVuY2F0aW9uUGVuY2lsLnRydW5jYXRpb25RdW90aWVudF9uYXREZWdyZWVfbGVfeXVrb25fYjZhMWRjZWQ5NGFjIiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoiYmV0dGVyLWNvZGVzLWhpc3RvcnkifQ]

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

/-- Multiplication by `X^s` transfers a degree bound on the residual side of
the identity back to the quotient. -/
theorem truncationQuotient_natDegree_le_yukon_b6a1dced94ac
    {N A s D : ℕ} {gamma r : F} {L R H E : Polynomial F}
    (hsN : s ≤ N) (hA : 1 ≤ A)
    (hgrid : L * R = Polynomial.X ^ N - 1)
    (htrunc : R = Polynomial.X ^ s * H +
      Polynomial.C r * Polynomial.X ^ (s - 1) + E)
    (hgamma : gamma * r = -1)
    (hresidual : (Polynomial.X ^ (s - 1) * L -
      Polynomial.X ^ (A + s - 1) - Polynomial.C gamma * L * E -
        Polynomial.C gamma).natDegree ≤ D + s) :
    (truncationQuotient N A s gamma L H).natDegree ≤ D  := by sorry
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize
