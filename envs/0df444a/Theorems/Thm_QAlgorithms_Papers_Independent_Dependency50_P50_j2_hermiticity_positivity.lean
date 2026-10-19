-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P50_j2_hermiticity_positivity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P50.j2_hermiticity_positivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:26:43.576736+00:00
-- url     : https://prove2.me/theorems/2acff315-5d12-414a-840e-8495df72305f
-- title:
--   Hermiticity and block-positivity criteria for J2
-- statement:
--   Let $n,m>0$, and let $T:M_n(\mathbb C)\to M_m(\mathbb C)$ be complex-linear. Define the unnormalized reference-first matrix $J_2(T)=\sum_{ij}E_{ij}\otimes T(E_{ij})$. A positive map sends every positive semidefinite matrix to a positive semidefinite matrix. The following two equivalences hold:
--
--   $$\begin{aligned}
--   T\text{ preserves Hermiticity}&\iff J_2(T)=J_2(T)^*,\\
--   T\text{ is positive}&\iff \langle J_2(T)(x\otimes y),x\otimes y\rangle\ge0\quad\text{for every }x\in\mathbb C^n,\ y\in\mathbb C^m.
--   \end{aligned}$$
--
--   The source scalar product is linear in its first argument, and a complex scalar being nonnegative requires that it be real as well as have nonnegative real part. The vectors are arbitrary. These criteria distinguish positivity on product vectors from positive semidefiniteness on all vectors.
-- source:
--   The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps, arXiv:quant-ph/0702255v1, PDF p. 6, Lemma 4

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P50

/-- PDF p.6, Lemma 4: Hermiticity and positivity criteria for the unnormalized
J2. ComplexOrder retains both reality and nonnegativity of each quadratic form. -/
theorem j2_hermiticity_positivity {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    (PreservesHermiticity T ↔ (j2 T).IsHermitian) ∧
      (Positive T ↔ ∀ (x : EuclideanSpace ℂ (Fin n)) (y : EuclideanSpace ℂ (Fin m)),
        0 ≤ inner ℂ (QAlgorithms.tensorVec x y)
          (QAlgorithms.act (j2 T) (QAlgorithms.tensorVec x y))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P50

end
