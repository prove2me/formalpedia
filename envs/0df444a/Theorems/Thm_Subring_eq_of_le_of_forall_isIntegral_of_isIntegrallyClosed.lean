-- Prove2me | Theorems.Thm_Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed
-- name    : Subring.eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/285066cd-1579-5b7b-b389-d3d75c0a8e46
-- title:
--   An integrally closed subring with fraction field F absorbs integral over-rings
-- statement:
--   Let $F$ be a field and let $B^\flat$ and $B$ be subrings of $F$ with $B^\flat \le B$. Assume that $F$ is a field of fractions of $B^\flat$, in the sense that the inclusion of $B^\flat$ into $F$ exhibits $F$ as the localisation of $B^\flat$ at its non-zero-divisors, and that $B^\flat$ is integrally closed, i.e. every element of its fraction field integral over $B^\flat$ lies in the image of $B^\flat$. Assume further that every element $b$ of $B$ is integral over $B^\flat$, that is, satisfies a monic polynomial with coefficients in $B^\flat$. The conclusion is the equality of subrings $B = B^\flat$. Thus under these hypotheses the inclusion $B^\flat \le B$ cannot be strict: a birational integral extension of an integrally closed subring of $F$ inside $F$ is trivial.
--
--   This is the standard fact that an integrally closed domain is its own integral closure inside its fraction field, packaged for subrings of a fixed field: a subring of $F$ integral over such a $B^\flat$ coincides with $B^\flat$. It is used in the verification that certain local rings attached to the modular curve $X_1$ are discrete valuation rings with the expected fraction field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Subring.eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed
    {F : Type*} [Field F] (Bflat B : Subring F) (hle : Bflat ≤ B)
    [IsFractionRing ↥Bflat F] [IsIntegrallyClosed ↥Bflat]
    (hint : ∀ b ∈ B, IsIntegral ↥Bflat b) :
    B = Bflat := by sorry
