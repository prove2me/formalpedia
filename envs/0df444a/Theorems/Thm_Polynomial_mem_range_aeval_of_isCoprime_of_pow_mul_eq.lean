-- Prove2me | Theorems.Thm_Polynomial_mem_range_aeval_of_isCoprime_of_pow_mul_eq
-- name    : Polynomial.mem_range_aeval_of_isCoprime_of_pow_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/3b6639f2-3cdc-5c9f-9c2a-99a3126a9117
-- title:
--   Coprime denominators: z is a polynomial in a transcendental x
-- statement:
--   Let $F$ be a field and $A$ a commutative ring that is a domain and an $F$-algebra. Let $x \in A$ be transcendental over $F$, i.e. the evaluation map $F[X] \to A$ sending $X \mapsto x$ is not injective on no nonzero polynomial — precisely, $x$ is not algebraic over $F$. Let $f, g \in F[X]$ be coprime in the Bézout sense (`IsCoprime f g`: there exist $u, v \in F[X]$ with $uf + vg = 1$), let $z \in A$, let $m, n$ be natural numbers, and let $P, Q \in F[X]$ be such that $f(x)^m z = P(x)$ and $g(x)^n z = Q(x)$, where $h(x)$ denotes the image of $h$ under the $F$-algebra evaluation map at $x$. The conclusion is that $z$ lies in the range of that evaluation map, i.e. $z = R(x)$ for some $R \in F[X]$. No positivity is assumed of $m$ or $n$, and $f$ or $g$ is allowed to be zero (in which case coprimality forces the other to be a unit).
--
--   This is the elementary statement that, inside a domain containing a transcendental element $x$ over $F$, an element with both an $f(x)$-power denominator and a $g(x)$-power denominator, for coprime $f, g$, is already a polynomial in $x$; equivalently $F[x][1/f(x)] \cap F[x][1/g(x)] = F[x]$. It is applied, with $f = X$ and $g = 1 - 16X$, in [`ModularCurve.minpoly_lambdaNModC_coeff_mem_adjoin`](thm.html#ModularCurve.minpoly_lambdaNModC_coeff_mem_adjoin) to show that certain coefficients, a priori rational functions with denominators supported at these two polynomials, lie in the polynomial ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_mem_range_aeval_of_isCoprime_of_pow_mul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem Polynomial.mem_range_aeval_of_isCoprime_of_pow_mul_eq
    {F A : Type*} [Field F] [CommRing A] [IsDomain A] [Algebra F A]
    (x : A) (hx : Transcendental F x) {f g : Polynomial F} (hfg : IsCoprime f g) (z : A) (m n : ℕ)
    (P Q : Polynomial F) (hf : Polynomial.aeval x f ^ m * z = Polynomial.aeval x P)
    (hg : Polynomial.aeval x g ^ n * z = Polynomial.aeval x Q) :
    z ∈ (Polynomial.aeval (R := F) x).range := by sorry
