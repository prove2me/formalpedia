-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P19_generalized_inverse_lower_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P19.generalized_inverse_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:03:52.677228+00:00
-- url     : https://prove2.me/theorems/12076517-1397-4d40-9dab-aeb8bc693a37
-- title:
--   A generalized-inverse Gram condition implies a positive operator lower bound
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, let $X$ be a positive semidefinite operator on $H$, let $K\ge1$ be an integer, and let $c\in\mathbb R$. Suppose that nonzero vectors $\xi_1,\ldots,\xi_K\in\operatorname{im}X$ satisfy $\langle\xi_j|X^{-1}|\xi_k\rangle=\delta_{jk}c$ for all $j,k$. Here $X^{-1}$ is the generalized inverse, which inverts the positive eigenvalues and vanishes on the kernel. Then
--
--   $$c>0,\qquad X\succeq\frac1c\sum_{k=1}^K|\xi_k\rangle\langle\xi_k|.$$
--
--   The vectors need not be normalized or orthogonal for the original Hilbert-space inner product. The result supplies the operator comparison used in the PGM optimality arguments.
--
--   **Formalization Note** The positive-index convention follows the source's induction beginning with $K=1$; the printed positivity assertion would fail for an empty collection.
-- source:
--   Optimality of the pretty good measurement for port-based teleportation, arXiv:2008.11194v2, PDF p. 4, Lemma 1 / Appendix A

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P19

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Extend50.P19

attribute [local instance] Classical.propDecidable

/-- Lemma 1, PDF pp.4 and 17 (Appendix A). K is positive: the source proof
starts at K=1, and the claimed positivity of c fails for an empty collection.
The vectors are nonzero and in im(X); they need not be normalized or
orthogonal in the ordinary inner product. -/
theorem generalized_inverse_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (hX : X.PosSemidef) (K : ℕ) (hK : 0 < K)
    (xi : Fin K → EuclideanSpace ℂ ι) (c : ℝ)
    (hxi : ∀ k, xi k ≠ 0 ∧ xi k ∈ LinearMap.range (Matrix.toEuclideanLin X))
    (hgram : ∀ j k, inner ℂ (xi j) (act (spectralInverse X) (xi k)) =
      if j = k then (c : ℂ) else 0) :
    0 < c ∧ (X - ((c⁻¹ : ℝ) : ℂ) • ∑ k, pureDensity (xi k)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Extend50.P19

end
