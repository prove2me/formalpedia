-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_admissibility_four_way
-- name    : QAlgorithms.Papers.Independent.Support21.P11.admissibility_four_way
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:57:04.874426+00:00
-- url     : https://prove2.me/theorems/047e768a-04bc-477c-8eae-5f321da50412
-- title:
--   The four equivalent admissibility conditions
-- statement:
--   Let $R$ be a commutative ring with identity, let $r\ge1$, let $\omega=(\omega_a)_{a\ge0}$ be an $R$-valued sequence, and let $u_1,\ldots,u_r\in R$. Write $W$ for the two-strand degenerate cyclotomic BMW algebra with these parameters, $e=e_1$, $s=s_1$, and $x=x_1$. Put $\prod_{i=1}^r(z-u_i)=\sum_{j=0}^r a_jz^j$. Assume that $2$ is invertible in $R$. Write $E=(x^ae)_{0\le a<r}$ and let $B$ be the indexed family of the three monomial types $x_1^ae_1x_1^b$, $x_1^ax_2^bs_1$, and $x_1^ax_2^b$, for $0\le a,b<r$. Here admissibility means both $\sum_{\mu=0}^{r-j-1}\omega_\mu a_{\mu+j+1}=-2\delta_{r-j\text{ odd}}a_j+\delta_{j\text{ even}}a_{j+1}$ for $0\le j<r$ and $\sum_{j=0}^ra_j\omega_{j+a}=0$ for every $a\ge0$. Define the Schur polynomials $q_a$ by $\prod_i(1+u_it)/(1-u_it)=\sum_{a\ge0}q_a(u)t^a$, and put $\eta_a(u)=q_{a+1}(u)-\tfrac12(-1)^rq_a(u)+\tfrac12\delta_{a,0}$. The symbol $\delta$ denotes the indicator of its subscripted condition. The parameters are called $u$-admissible when $\omega_a=\eta_a(u)$ for every $a\ge0$. Then
--
--   $$
--   E\text{ is linearly independent}\ \Longleftrightarrow\ B\text{ is linearly independent}\ \Longleftrightarrow\ (\omega,u)\text{ is admissible}\ \Longleftrightarrow\ (\omega,u)\text{ is }u\text{-admissible}.
--   $$
--
--   This identifies parameter admissibility with independence of the explicit families in the two-strand algebra.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 8, Theorem 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Theorem 5.2, PDF p.8: all four conditions are conclusions, with no
admissibility or independence premise; 2 is invertible in the ground ring. -/
theorem admissibility_four_way (R : Type*) [CommRing R] (omega : ℕ → R)
    (r : ℕ) (u : Fin r → R) (hr : 1 ≤ r) (h2 : IsUnit (2 : R)) :
    (LinearIndependent R (idealFamily R omega r u) ↔
      LinearIndependent R (algebraFamily R omega r u)) ∧
    (LinearIndependent R (algebraFamily R omega r u) ↔ BMWAdmissible omega u) ∧
    (BMWAdmissible omega u ↔ UAdmissible omega u) := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
