-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_admissible_iff_u_admissible
-- name    : QAlgorithms.Papers.Independent.Support21.P11.admissible_iff_u_admissible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:01:36.158634+00:00
-- url     : https://prove2.me/theorems/50810cb8-5542-481f-add3-081fd5d70dcd
-- title:
--   Admissibility equals u-admissibility
-- statement:
--   Let $R$ be a commutative ring with identity, let $r\ge1$, let $\omega=(\omega_a)_{a\ge0}$ be an $R$-valued sequence, and let $u_1,\ldots,u_r\in R$. Write $W$ for the two-strand degenerate cyclotomic BMW algebra with these parameters, $e=e_1$, $s=s_1$, and $x=x_1$. Put $\prod_{i=1}^r(z-u_i)=\sum_{j=0}^r a_jz^j$. Assume $2$ is invertible in $R$. Here admissibility means both $\sum_{\mu=0}^{r-j-1}\omega_\mu a_{\mu+j+1}=-2\delta_{r-j\text{ odd}}a_j+\delta_{j\text{ even}}a_{j+1}$ for $0\le j<r$ and $\sum_{j=0}^ra_j\omega_{j+a}=0$ for every $a\ge0$. Define the Schur polynomials $q_a$ by $\prod_i(1+u_it)/(1-u_it)=\sum_{a\ge0}q_a(u)t^a$, and put $\eta_a(u)=q_{a+1}(u)-\tfrac12(-1)^rq_a(u)+\tfrac12\delta_{a,0}$. The symbol $\delta$ denotes the indicator of its subscripted condition. Then
--
--   $$(\omega,u)\text{ is admissible}\quad\Longleftrightarrow\quad\omega_a=\eta_a(u)\text{ for every }a\ge0.$$
--
--   The right-hand condition is $u$-admissibility. This identifies the predicates over arbitrary commutative ground rings in which $2$ is invertible, including repeated and zero parameters.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 8, Lemma 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 5.1, PDF p.8: the paper's two admissibility predicates are equivalent. -/
theorem admissible_iff_u_admissible (R : Type*) [CommRing R] (omega : ℕ → R)
    (r : ℕ) (u : Fin r → R) (hr : 1 ≤ r) (h2 : IsUnit (2 : R)) :
    BMWAdmissible omega u ↔ UAdmissible omega u := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
