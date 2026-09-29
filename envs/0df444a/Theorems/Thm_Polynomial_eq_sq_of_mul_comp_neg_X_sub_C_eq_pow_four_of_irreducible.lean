-- Prove2me | Theorems.Thm_Polynomial_eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible
-- name    : Polynomial.eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/2bda89a6-ee4c-55bf-80f9-4aeeab3fdd17
-- title:
--   A quartic functional equation forces P = N²
-- statement:
--   Let $t, n$ be integers and set $N := X^2 + tX + n \in \mathbb{Q}[X]$, the coefficients $t$ and $n$ being taken as rational constants. Suppose that $N$ is irreducible in $\mathbb{Q}[X]$, and let $P \in \mathbb{Q}[X]$ be a polynomial whose natural degree is at most $4$ and which satisfies the functional equation $$P(X) \cdot P(-X - t) = N(X)^4,$$ where the second factor is the composite of $P$ with the polynomial $-X - t$. Assume furthermore that $P$ takes a strictly positive value at some integer, i.e. there is $m \in \mathbb{Z}$ with $P(m) > 0$ in $\mathbb{Q}$. Then $P$ is exactly the square of the quadratic, $P = (X^2 + tX + n)^2$. In particular the normalisation is pinned down: the sign ambiguity $P = \pm N^2$ allowed by the functional equation alone is resolved by the positivity hypothesis.
--
--   An elementary rigidity statement about degree-four solutions of a multiplicative functional equation attached to an irreducible integral quadratic. It is used in the Čerednik–Drinfeld part of the development, in [`CerednikDrinfeld.QM.isFinite_endKerStr_act_and_finrank_eq_natAbs_sq`](thm.html#CerednikDrinfeld.QM.isFinite_endKerStr_act_and_finrank_eq_natAbs_sq), to identify a characteristic-polynomial-type quartic as the square of a quadratic and thereby compute a rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible
    (t n : ℤ) (P : Polynomial ℚ)
    (hirr : Irreducible (X ^ 2 + C (t : ℚ) * X + C (n : ℚ) : Polynomial ℚ))
    (hP : P.natDegree ≤ 4)
    (hPQ : P * P.comp (-X - C (t : ℚ)) = (X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 4)
    (hpos : ∃ m : ℤ, 0 < P.eval (m : ℚ)) :
    P = (X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 2 := by sorry
