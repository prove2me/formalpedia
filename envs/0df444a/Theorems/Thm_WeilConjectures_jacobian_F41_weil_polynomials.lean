-- Prove2me | Theorems.Thm_WeilConjectures_jacobian_F41_weil_polynomials
-- name    : WeilConjectures.jacobian_F41_weil_polynomials
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T15:01:10.881595+00:00
-- url     : https://prove2.me/theorems/2eae46b2-6cb9-411a-8606-9ffe007fa865
-- title:
--   Weil polynomials of the Jacobian of $y^2+y=x^5$ over $\mathbb F_{41}$
-- statement:
--   Let $\alpha_1,\dots,\alpha_4\in\mathbb C$ be such that $1-9T+71T^2-9\cdot41T^3+41^2T^4=\prod_{j=1}^4(1-\alpha_jT)$, and put
--
--   $$W_i(T)=\prod_{1\le j_1<\cdots<j_i\le4}\big(1-\alpha_{j_1}\cdots\alpha_{j_i}T\big),\qquad i=0,\dots,4.$$
--
--   Then
--
--   1. $W_0=1-T$;
--   2. $W_1=1-3^2T+71T^2-3^2\cdot41T^3+41^2T^4$;
--   3. $W_2=(1-41T)^2(1+11T+3\cdot7\cdot41T^2+11\cdot41^2T^3+41^4T^4)$;
--   4. $W_3=1-3^2\cdot41T+71\cdot41^2T^2-3^2\cdot41^4T^3+41^6T^4$;
--   5. $W_4=1-41^2T$.
--
--   In the source these $W_i$ are the Weil polynomials $P_i$ of the abelian surface $\operatorname{Jac}(C/\mathbb F_{41})$.
--
--   **Formalization Note** Only the polynomial identities are formalized; the identification of the $W_i$ with the zeta function of the Jacobian is not stated, since Mathlib has no Jacobians. The products run over sub-multisets of size $i$ of the multiset $\{\alpha_j\}$.
-- source:
--   Wikipedia, "Weil conjectures", https://en.wikipedia.org/wiki/Weil_conjectures (PDF snapshot supplied by the proposer, 14 pp.), section "Examples", subsection "Abelian surfaces" (formula for $P_i(T)$ and the list $P_0,\dots,P_4$)

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

open AlgebraicGeometry CategoryTheory Polynomial

namespace WeilConjectures

theorem jacobian_F41_weil_polynomials (α : Multiset ℂ)
    (hα : (1 - 9 * Polynomial.X + 71 * Polynomial.X ^ 2 - 9 * 41 * Polynomial.X ^ 3 +
          41 ^ 2 * Polynomial.X ^ 4 : ℂ[X]) = (α.map fun a => 1 - C a * Polynomial.X).prod) :
    let W : ℕ → ℂ[X] := fun i => ((α.powersetCard i).map fun s => 1 - C s.prod * Polynomial.X).prod
    W 0 = 1 - Polynomial.X ∧
    W 1 = 1 - 3 ^ 2 * Polynomial.X + 71 * Polynomial.X ^ 2 - 3 ^ 2 * 41 * Polynomial.X ^ 3 +
      41 ^ 2 * Polynomial.X ^ 4 ∧
    W 2 = (1 - 41 * Polynomial.X) ^ 2 * (1 + 11 * Polynomial.X + 3 * 7 * 41 * Polynomial.X ^ 2 +
      11 * 41 ^ 2 * Polynomial.X ^ 3 + 41 ^ 4 * Polynomial.X ^ 4) ∧
    W 3 = 1 - 3 ^ 2 * 41 * Polynomial.X + 71 * 41 ^ 2 * Polynomial.X ^ 2 -
      3 ^ 2 * 41 ^ 4 * Polynomial.X ^ 3 + 41 ^ 6 * Polynomial.X ^ 4 ∧
    W 4 = 1 - 41 ^ 2 * Polynomial.X := by sorry

end WeilConjectures
