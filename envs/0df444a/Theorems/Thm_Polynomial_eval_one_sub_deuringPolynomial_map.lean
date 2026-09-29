-- Prove2me | Theorems.Thm_Polynomial_eval_one_sub_deuringPolynomial_map
-- name    : Polynomial.eval_one_sub_deuringPolynomial_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/ae8654fc-747f-5fc3-b131-2444edac05ee
-- title:
--   Functional equation H_q(1-t)=(-1)^m H_q(t) in characteristic q
-- statement:
--   Let $q$ be a prime number and let $F$ be a field of characteristic $q$. Write $m = (q-1)/2$ for the natural-number quotient, and let $H_q \in \mathbb{Z}[X]$ be the Deuring polynomial $$H_q = \sum_{i=0}^{m} \binom{m}{i}^{2} X^{i},$$ that is, `deuringPolynomial q`, the polynomial with integer coefficient $\binom{m}{i}^2$ in degree $i$ for $0 \le i \le m$. Let $H_q^F$ denote its image under the coefficientwise map induced by the ring homomorphism $\mathbb{Z} \to F$. The assertion is that for every $t \in F$, $$H_q^F(1-t) = (-1)^{m}\, H_q^F(t),$$ an identity in $F$. Thus the substitution $t \mapsto 1-t$ changes the value of the reduction of the Deuring polynomial only by the sign $(-1)^{(q-1)/2}$; in particular the set of zeros of $H_q^F$ in $F$ is stable under $t \mapsto 1-t$. For $q = 2$ one has $m = 0$ and $H_2 = 1$, so the statement is trivial in that case.
--
--   This is one of the two functional equations of the Deuring (Hasse) polynomial whose roots are the supersingular parameters of the Legendre family $y^2 = x(x-1)(x-\lambda)$ in characteristic $q$; together with the palindromic symmetry it expresses stability of the supersingular locus under the anharmonic group of order six. It is used in [`ModularCurve.sum_inv_jWidth_of_deuringPolynomial`](thm.html#ModularCurve.sum_inv_jWidth_of_deuringPolynomial), on the way from counting supersingular $\lambda$-values to the Eichler–Deuring mass formula for supersingular $j$-invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_eval_one_sub_deuringPolynomial_map.lean

import Mathlib
import Definitions.Def_Polynomial_DeuringPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem Polynomial.eval_one_sub_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) [Fact q.Prime]
    [CharP F q] (t : F) :
    ((deuringPolynomial q).map (Int.castRingHom F)).eval (1 - t)
      = (-1) ^ ((q - 1) / 2) * ((deuringPolynomial q).map (Int.castRingHom F)).eval t := by sorry
