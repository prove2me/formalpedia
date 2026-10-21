-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_schur_integrality
-- name    : QAlgorithms.Papers.Independent.Support21.P12.schur_integrality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:07:36.746991+00:00
-- url     : https://prove2.me/theorems/5b86c8d3-c206-494c-9bd9-0795be7092d4
-- title:
--   Schur q congruence and integral eta polynomials
-- statement:
--   Fix $r\ge1$ and independent indeterminates $u_1,\ldots,u_r$ over $\mathbb Z$. Define $q_a$ by $\prod_i(1+u_it)/(1-u_it)=\sum_{a\ge0}q_at^a$, and let $p_a=\sum_i u_i^a$. In $\mathbb Q[u_1,\ldots,u_r]$, put $\eta_a^\pm=q_{a+1}\pm(-1)^{r-1}q_a/2+\delta_{a,0}/2$. Then
--
--   $$q_0=1,\qquad q_a-2p_a\in4\mathbb Z[u_1,\ldots,u_r]\ (a\ge1),\qquad \eta_a^\pm\in\mathbb Z[u_1,\ldots,u_r]\ (a\ge0).$$
--
--   Both signs are included. The integral lift is obtained by halving integer coefficients of the even numerator, so it can subsequently be evaluated without inverting two.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 6, Lemma 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Lemma 3.3, all three parts, PDF p.6. Integrality is stated through the
explicit integral lift and includes BOTH signs. -/
theorem schur_integrality (r : ℕ) (hr : 0 < r) :
    schurQ r 0 = 1 ∧
    (∀ a : ℕ, 1 ≤ a → ∃ p : MvPolynomial (Fin r) ℤ,
      schurQ r a - 2 * powerSum r a = 4 * p) ∧
    (∀ a : ℕ, ∀ plus : Bool,
      MvPolynomial.map (Int.castRingHom ℚ) (etaIntegral r a plus) = etaRational r a plus) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
