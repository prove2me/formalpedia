-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P14_cauchy_unique_gamma
-- name    : QAlgorithms.Papers.Independent.Support21.P14.cauchy_unique_gamma
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:29:24.59788+00:00
-- url     : https://prove2.me/theorems/e69256a6-bd2a-423f-ae5a-f324d4ed7ccd
-- title:
--   Explicit unique solution of the Cauchy system
-- statement:
--   Let $F$ be a field, $r\ge1$, and $u_1,\ldots,u_r\in F$ distinct and nonzero, with $u_i u_j\ne1$ for every pair, including $i=j$. Let $\rho,q\in F$ be nonzero with $q^2\ne1$. Put $C_{ij}=(1-u_i u_j)^{-1}$ and $P_j=\prod_{\ell\ne j}(u_\ell u_j-1)/(u_j-u_\ell)$.
--
--   Define
--   $$\gamma_j=P_j\left(\frac{1-u_j^2}{\rho(q^{-1}-q)}\prod_{\ell\ne j}u_\ell+\begin{cases}1,&r\text{ odd},\\-u_j,&r\text{ even}.\end{cases}\right).$$
--   The vector $\gamma$ is the unique solution of
--   $$\sum_{j=1}^r C_{ij}\gamma_j=\frac1{1-u_i^2}+\frac1{\rho(q^{-1}-q)}\quad(1\le i\le r).$$
--   This explicit inverse-system calculation needs no ground-ring or admissibility relation.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, II: Admissibility Relations and Freeness, arXiv:math/0612065v5, PDF p. 19, Lemma 3.9: explicit unique solution of the Cauchy system

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P14

/-- Lemma 3.9, PDF p.19. The formula is a solution and the only solution.
No ground-ring relation involving rho,q,delta is required. -/
theorem cauchy_unique_gamma {F : Type*} [Field F] (r : ℕ) (hr : 0 < r)
    (u : Fin r → F) (hu : Function.Injective u) (hzero : ∀ j, u j ≠ 0)
    (hprod : ∀ i j, u i * u j ≠ 1) (rho q : F)
    (hrho : rho ≠ 0) (hq : q ≠ 0) (hsquare : q^2 ≠ 1) :
    ∀ gamma : Fin r → F,
      (∀ i, ∑ j : Fin r, cauchyMatrix u i j * gamma j =
        (1-u i^2)⁻¹ + (rho*(q⁻¹-q))⁻¹) ↔ gamma = gammaVector u rho q := by sorry

end QAlgorithms.Papers.Independent.Support21.P14

end
