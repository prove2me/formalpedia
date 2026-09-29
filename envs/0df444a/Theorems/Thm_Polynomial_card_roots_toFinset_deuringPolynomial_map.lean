-- Prove2me | Theorems.Thm_Polynomial_card_roots_toFinset_deuringPolynomial_map
-- name    : Polynomial.card_roots_toFinset_deuringPolynomial_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/881265a8-25ad-5524-bb13-e746b8c00760
-- title:
--   The Deuring polynomial has (q-1)/2 distinct roots in characteristic q
-- statement:
--   Let $F$ be an algebraically closed field and let $q$ be a prime number such that $F$ has characteristic $q$; write $m = (q-1)/2$ for the natural-number quotient. The Deuring polynomial is the integral polynomial $\sum_{i=0}^{m} \binom{m}{i}^{2} X^{i} \in \mathbb{Z}[X]$, and it is pushed forward to $F[X]$ along the canonical ring homomorphism $\mathbb{Z} \to F$. The assertion is that the multiset of roots of this image in $F$, regarded as a finite set (that is, with multiplicities discarded), has exactly $m$ elements. Equivalently, the number of $\alpha \in F$ with $\sum_{i=0}^{m} \binom{m}{i}^{2} \alpha^{i} = 0$ is $(q-1)/2$. Since the degree of the image is at most $m$, this simultaneously records that the reduction has degree exactly $m$ and that it is separable, i.e. has no repeated roots in characteristic $q$.
--
--   This is the combination of Igusa's results that the Deuring polynomial $H_q$ has degree $(q-1)/2$ and is separable modulo $q$; its roots are exactly the parameters $\lambda$ for which the Legendre curve $y^2 = x(x-1)(x-\lambda)$ is supersingular over $F$. It is used in the derivation of the Eichler–Deuring mass formula, through [`ModularCurve.sum_inv_jWidth_of_deuringPolynomial`](thm.html#ModularCurve.sum_inv_jWidth_of_deuringPolynomial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_card_roots_toFinset_deuringPolynomial_map.lean

import Mathlib
import Definitions.Def_Polynomial_DeuringPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem Polynomial.card_roots_toFinset_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) [IsAlgClosed F]
    [DecidableEq F] [Fact q.Prime] [CharP F q] :
    ((deuringPolynomial q).map (Int.castRingHom F)).roots.toFinset.card = (q - 1) / 2 := by sorry
