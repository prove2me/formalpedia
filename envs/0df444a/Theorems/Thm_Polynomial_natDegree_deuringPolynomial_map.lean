-- Prove2me | Theorems.Thm_Polynomial_natDegree_deuringPolynomial_map
-- name    : Polynomial.natDegree_deuringPolynomial_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/45f8cf00-e31d-5e5a-b274-03206e87b7d8
-- title:
--   Degree of the Deuring polynomial over any field
-- statement:
--   Let $F$ be a field and let $q$ be a natural number. Write $m = (q-1)/2$ for the natural-number quotient of the truncated difference $q-1$ by $2$, and let $$H_q(X) = \sum_{i=0}^{m} \binom{m}{i}^{2} X^{i} \in \mathbb{Z}[X]$$ be the Deuring polynomial `deuringPolynomial q`, the sum over $i$ in the range $0,\dots,m$ of the constant $\binom{m}{i}^{2}$, viewed in $\mathbb{Z}$, times $X^{i}$. The assertion is that the image of $H_q$ in $F[X]$ under the coefficientwise map induced by the unique ring homomorphism $\mathbb{Z} \to F$ has `natDegree` equal to $m = (q-1)/2$. In particular no degree drop occurs in any characteristic, the $q$-th case being recorded uniformly for all natural numbers $q$ (no primality or positivity is assumed; for $q = 0$ and $q = 1$ both sides are $0$, the polynomial being the constant $1$). The statement concerns `natDegree`, so it carries no information about whether the reduction is nonzero beyond what the value $m$ records.
--
--   The polynomial $H_q$ is the Deuring, or Hasse, polynomial whose roots in characteristic $q$ are the Legendre parameters $\lambda$ of supersingular elliptic curves; its degree $(q-1)/2$ is the classical count underlying the supersingular mass formula. The degree statement is used in the construction of a supersingular endomorphism with prescribed cyclic kernel of odd prime-power order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_natDegree_deuringPolynomial_map.lean

import Mathlib
import Definitions.Def_Polynomial_DeuringPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem Polynomial.natDegree_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) :
    ((deuringPolynomial q).map (Int.castRingHom F)).natDegree = (q - 1) / 2 := by sorry
