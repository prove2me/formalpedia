-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P14_cauchy_inverse_vectors
-- name    : QAlgorithms.Papers.Independent.Support21.P14.cauchy_inverse_vectors
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:31:00.675651+00:00
-- url     : https://prove2.me/theorems/e6972da8-27d4-4b63-b2cd-6e50b41b8c5b
-- title:
--   Cauchy invertibility and its two explicit inverse vectors
-- statement:
--   Let $F$ be a field, $r\ge1$, and let $u_1,\ldots,u_r\in F$ be distinct nonzero elements with $u_i u_j\ne1$ for all pairs, including the diagonal. Put $C_{ij}=(1-u_i u_j)^{-1}$ and $P_j=\prod_{\ell\ne j}(u_\ell u_j-1)/(u_j-u_\ell)$.
--
--   The matrix $C$ is invertible. The unique solutions $\gamma^{(1)}$ and $\gamma^{(2)}$ of $C\gamma^{(1)}=\mathbf1$ and $C\gamma^{(2)}=((1-u_i^2)^{-1})_i$, respectively, are
--   $$\gamma_j^{(1)}=(1-u_j^2)\left(\prod_{\ell\ne j}u_\ell\right)P_j,$$
--   $$\gamma_j^{(2)}=\begin{cases}P_j,&r\text{ odd},\\-u_jP_j,&r\text{ even}.\end{cases}$$
--   Both invertibility and uniqueness are conclusions. These vectors give the explicit inverse calculations underlying the admissibility coefficients.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, II: Admissibility Relations and Freeness, arXiv:math/0612065v5, PDF p. 24, Lemma 3.15: Cauchy invertibility and two explicit inverse vectors

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P14

/-- Lemma 3.15, PDF pp.24--25. Invertibility and both unique solutions,
including the odd and even cases of the second vector. -/
theorem cauchy_inverse_vectors {F : Type*} [Field F] (r : ℕ) (hr : 0 < r)
    (u : Fin r → F) (hu : Function.Injective u) (hzero : ∀ j, u j ≠ 0)
    (hprod : ∀ i j, u i * u j ≠ 1) :
    IsUnit (cauchyMatrix u) ∧
    (∀ gamma : Fin r → F,
      (∀ i, ∑ j : Fin r, cauchyMatrix u i j * gamma j = 1) ↔ gamma = cauchyFirstVector u) ∧
    (∀ gamma : Fin r → F,
      (∀ i, ∑ j : Fin r, cauchyMatrix u i j * gamma j = (1-u i^2)⁻¹) ↔
        gamma = cauchySecondVector u) := by sorry

end QAlgorithms.Papers.Independent.Support21.P14

end
