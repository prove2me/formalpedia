-- Prove2me | Theorems.Thm_PolyTimeFactorization_congruent_squares_split
-- name    : PolyTimeFactorization.congruent_squares_split
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T16:12:44.382202+00:00
-- url     : https://prove2.me/theorems/9759f763-9d6a-4655-886a-05e97df6f27b
-- title:
--   A nontrivial congruence of squares splits $n$ (QS / GNFS)
-- statement:
--   Let $n\ge 1$ and $x,y\in\mathbb{Z}$. If $x^2\equiv y^2\pmod n$ but $x\not\equiv y\pmod n$ and $x\not\equiv -y\pmod n$, then
--   $$1<\gcd(x-y,\,n)<n,$$
--   so $\gcd(x-y,n)$ is a nontrivial divisor of $n$.
--
--   This is the splitting step that concludes both the quadratic sieve and the number field sieve: once a congruence of squares is found that is nontrivial modulo $n$, a single gcd reveals a proper factor. The two exclusions $x\not\equiv\pm y\pmod n$ are exactly what rules out the trivial factors $1$ and $n$.
-- source:
--   C. Pomerance, The quadratic sieve factoring algorithm, EUROCRYPT '84, LNCS 209 (1985), 169-182, https://doi.org/10.1007/3-540-39757-4_17 ; J. P. Buhler, H. W. Lenstra Jr., C. Pomerance, Factoring integers with the number field sieve, LNM 1554 (1993), 50-94, https://doi.org/10.1007/BFb0091539 (the congruence-of-squares principle)

import Mathlib

namespace PolyTimeFactorization

theorem congruent_squares_split (n : ℕ) (x y : ℤ) (hn : 0 < n)
    (hsq : (n : ℤ) ∣ x ^ 2 - y ^ 2)
    (hxy : ¬ (n : ℤ) ∣ x - y) (hxy' : ¬ (n : ℤ) ∣ x + y) :
    1 < Int.gcd (x - y) (n : ℤ) ∧ Int.gcd (x - y) (n : ℤ) < n := by sorry

end PolyTimeFactorization
