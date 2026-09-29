-- Prove2me | Theorems.Thm_Polynomial_aeval_pow_card_eq_pow_card
-- name    : Polynomial.aeval_pow_card_eq_pow_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/5ff51740-8719-5f89-964e-12bec0f9466e
-- title:
--   q-power map commutes with polynomial evaluation over 𝔽_q
-- statement:
--   Let $F$ be a field which is finite as a type, write $q =$ `Fintype.card F` for its cardinality, let $E$ be a commutative ring equipped with an $F$-algebra structure, let $p \in F[X]$ be a polynomial with coefficients in $F$, and let $x \in E$. The assertion is that evaluating $p$ (via the algebra map $F \to E$) at the $q$-th power $x^{q}$ gives the same element of $E$ as raising the value $p(x)$ to the $q$-th power: $\mathrm{aeval}_{x^{q}}(p) = (\mathrm{aeval}_x(p))^{q}$. No hypothesis beyond the finiteness of $F$, the commutativity of $E$ and the $F$-algebra structure is imposed; in particular $E$ need not be reduced, an integral domain, or of characteristic equal to that of $F$ in any further sense, and $p$ is arbitrary.
--
--   This is the statement that the $q$-power map commutes with evaluation of polynomials defined over the field $\mathbb{F}_q$ with $q$ elements, the algebraic input to the fact that the Frobenius orbit of a root of such a polynomial consists again of roots. It is used in the local analysis of residue fields, where it is applied to the minimal polynomial of an element to show that $x^{q}$ is again a root.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_aeval_pow_card_eq_pow_card.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.aeval_pow_card_eq_pow_card
    (F : Type) [Field F] [Fintype F] (E : Type) [CommRing E] [Algebra F E] (p : F[X]) (x : E) :
    Polynomial.aeval (x ^ Fintype.card F) p = (Polynomial.aeval x p) ^ Fintype.card F := by sorry
