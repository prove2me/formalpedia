-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_universalH_explicit_schur
-- name    : QAlgorithms.Papers.Independent.Support21.P11.universalH_explicit_schur
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:03:32.030985+00:00
-- url     : https://prove2.me/theorems/da3b2e92-34f7-4368-af1f-139e6caa0913
-- title:
--   Explicit Schur formula for the universal integer sequence
-- statement:
--   Let $R$ be a commutative unital ring in which $2$ is invertible, let $r\ge1$, and let $u_1,\ldots,u_r\in R$ be arbitrary. Let $a_j$ be the coefficients of $\prod_i(z-u_i)$ and let $H_a\in\mathbb Z[u_1,\ldots,u_r]$ be the reverse triangular and monic recurrence construction of Lemma 4.4. Define the Schur polynomials $q_a$ by $\prod_i(1+u_it)/(1-u_it)=\sum_{a\ge0}q_a(u)t^a$, and put $\eta_a(u)=q_{a+1}(u)-\tfrac12(-1)^rq_a(u)+\tfrac12\delta_{a,0}$. The symbol $\delta$ denotes the indicator of its subscripted condition. Then
--
--   $$H_a(u)=\eta_a(u)\quad(a\ge0),$$
--   $$\sum_{\mu=0}^{r-j-1}\eta_\mu(u)a_{\mu+j+1}(u)=-2\delta_{r-j\text{ odd}}a_j(u)+\delta_{j\text{ even}}a_{j+1}(u)\quad(0\le j<r),$$
--   $$\sum_{\mu=0}^ra_\mu(u)\eta_{\mu+a}(u)=0\quad(a\ge0).$$
--
--   These formulas identify the integral universal sequence after evaluation in any such ground ring; no separately chosen sequence $\omega$ or admissibility hypothesis is required.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 8, §5, explicit H and equations (5.7)–(5.8)

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Section 5, unnumbered explicit-H result and (5.7)--(5.8), PDF pp.7--8.
The omega sequence is not an input; arbitrary repeated and zero u_i are permitted. -/
theorem universalH_explicit_schur (R : Type*) [CommRing R]
    (r : ℕ) (u : Fin r → R) (hr : 1 ≤ r) (h2 : IsUnit (2 : R)) :
    (∀ a : ℕ, evalH u a = schurEta u a) ∧
    TriangularRelations (schurEta u) u ∧ CyclotomicRecurrence (schurEta u) u := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
