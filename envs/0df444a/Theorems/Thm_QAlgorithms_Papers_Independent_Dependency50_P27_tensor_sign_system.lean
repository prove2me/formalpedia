-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_tensor_sign_system
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.tensor_sign_system
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:57:28.237487+00:00
-- url     : https://prove2.me/theorems/1ecd1b60-f91c-43c3-b05b-ad186409a7fc
-- title:
--   §5.4, unnumbered tensor sign-determination system
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Let $Q_1,\ldots,Q_n$ be a finite family, and let $z$ be a finite list. Index signs by $\sigma\in\{1,-1,0\}^n$ and powers by $\epsilon\in\{1,2,0\}^n$ in those coordinate orders. Let $c_\sigma$ count list occurrences realizing all signs, and let $t_\epsilon=\operatorname{TaQ}(z,\prod_k Q_k^{\epsilon_k})$. With $M=\left(\begin{smallmatrix}1&1&1\\-1&1&1\\0&0&1\end{smallmatrix}\right)$,
--
--   $$t=cM^{\otimes n},\qquad (M^{\otimes n})_{\sigma,\epsilon}=\prod_k M_{\sigma_k,\epsilon_k}.$$
--
--   The tensor matrix $M^{\otimes n}$ is invertible for every $n$. At $n=0$ the matrix is the one-dimensional identity and each row vector has the single entry $|z|$.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 27, §5.4, unnumbered tensor sign-determination system

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF pp. 27–28, the tensor sign-determination system and invertibility.
The printed prose calls cvec a Cauchy-index vector and size(sQ) the length of z;
use sign counts and the number of polynomials, as fixed by the displayed induction
and its empty-family base case. No change to the displayed identity is needed. -/
theorem tensor_sign_system {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (n : ℕ) (qs : Fin n → Polynomial R) (z : List R) :
    tvec z qs = Matrix.vecMul (cvec z qs) (tensorMatrix n) ∧
    IsUnit (tensorMatrix n) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
