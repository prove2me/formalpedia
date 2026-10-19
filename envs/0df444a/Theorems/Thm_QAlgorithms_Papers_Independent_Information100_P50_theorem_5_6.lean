-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_theorem_5_6
-- name    : QAlgorithms.Papers.Independent.Information100.P50.theorem_5_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:06:07.175442+00:00
-- url     : https://prove2.me/theorems/de724b73-baa0-4278-899b-51e7de75fc85
-- title:
--   Theorem 5.6: For a Kubo–Ando mean with representing f_sigma, if f_sigma(0+)=f_sigma'(infinity)=0, then range(A sigma B)=ran
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   A Kubo–Ando mean $\sigma$ has a nonnegative operator-monotone representing function $f_\sigma$ with $f_\sigma(1)=1$. Set $g_\sigma(t)=t f_\sigma((1-t)/t)$ for $0<t<1$, $g_\sigma(0)=f_\sigma'(\infty)$, and $g_\sigma(1)=f_\sigma(0+)$. Matrix functions use spectral functional calculus and singular means use decreasing positive regularization.
--
--   If $f_\sigma(0+)=f_\sigma'(\infty)=0$, then for all PSD matrices $A,B$ in every finite dimension,
--
--   $$\operatorname{range}(A\sigma B)=\operatorname{range}(A)\cap\operatorname{range}(B),\qquad A\sigma B=0\iff\operatorname{range}(A)\cap\operatorname{range}(B)=\{0\}.$$
--
--   Conversely, in any fixed dimension at least two, if $A\sigma B=0$ for every PSD pair with trivially intersecting ranges, then both endpoint quantities are zero. The converse is universal over pairs, rather than an assertion about one vanishing example. This characterizes the distinct-range property.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 19, Theorem 5.6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Theorem 5.6, source PDF p.19, including the universal converse on any fixed
matrix space of dimension at least two. -/
theorem theorem_5_6 (s : Mean) :
    ((atZero s.f = 0 ∧ atInfinity s.f = 0) → ∀ (n : ℕ) (A B : M n),
      A.PosSemidef → B.PosSemidef →
      matrixRange (connectionOp s.toConnection A B) = matrixRange A ⊓ matrixRange B ∧
      (connectionOp s.toConnection A B = 0 ↔ matrixRange A ⊓ matrixRange B = ⊥)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (∀ A B : M n, A.PosSemidef → B.PosSemidef →
        matrixRange A ⊓ matrixRange B = ⊥ → connectionOp s.toConnection A B = 0) →
      atZero s.f = 0 ∧ atInfinity s.f = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
