-- Prove2me | Theorems.Thm_Polynomial_separable_deuringPolynomial_map
-- name    : Polynomial.separable_deuringPolynomial_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/3c04a282-09ff-51cd-bc1a-549341ad33d9
-- title:
--   Separability of the Deuring polynomial in characteristic q
-- statement:
--   Let $F$ be a field and let $q$ be a natural number which is prime, with $F$ of characteristic $q$. Write $m = (q-1)/2$ for the natural-number quotient, so $m$ is the integer part of $(q-1)/2$, and consider the Deuring polynomial
--   $$H_q(X) \;=\; \sum_{i=0}^{m} \binom{m}{i}^{2} X^{i} \in \mathbb{Z}[X],$$
--   the sum over $i$ in the range $0,\dots,m$ of the constant $\binom{m}{i}^{2}$, viewed as an integer, times $X^{i}$. The assertion is that the image of $H_q$ in $F[X]$ under the coefficientwise map induced by the canonical ring homomorphism $\mathbb{Z} \to F$ is separable in the sense of Mathlib's `Polynomial.Separable`, that is, this image and its formal derivative are coprime in $F[X]$. No hypothesis of perfection, algebraic closure or finiteness is imposed on $F$; only that its characteristic is the prime $q$. For $q = 2$ one has $m = 0$ and the polynomial is the constant $1$, for which the conclusion is immediate.
--
--   This is Igusa's theorem that the Deuring (Hasse) polynomial of the Legendre family of elliptic curves has only simple roots in characteristic $q$. It is used in the analysis of the Hasse invariant of the Legendre family, both to locate curves with nonzero Hasse invariant and to show that the roots of the Hasse invariant along the $j$-family have multiplicity one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_separable_deuringPolynomial_map.lean

import Mathlib
import Definitions.Def_Polynomial_DeuringPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem Polynomial.separable_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) [Fact q.Prime]
    [CharP F q] : ((deuringPolynomial q).map (Int.castRingHom F)).Separable := by sorry
