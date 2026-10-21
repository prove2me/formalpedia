-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P19_saturation_minimal_capacity
-- name    : QAlgorithms.Papers.Independent.Next46.P19.saturation_minimal_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:32:43.403614+00:00
-- url     : https://prove2.me/theorems/4cccc522-771c-4c52-82a1-4772a872cc3e
-- title:
--   Saturation of one Robertson–Schrödinger inequality gives minimal symplectic capacity
-- statement:
--   Let $n\ge1$ and $\hbar>0$. Use grouped phase-space coordinates $z=(x_1,\ldots,x_n,p_1,\ldots,p_n)$ on $\mathbb R^{2n}$ and let $J=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$. Let $\Sigma$ be a real symmetric positive definite $2n\times2n$ matrix satisfying the physical uncertainty condition $\Sigma+\frac{i\hbar}{2}J\succeq0$, where positivity is Hermitian positive semidefiniteness. Suppose some $j\in\{1,\ldots,n\}$ satisfies $\Sigma_{x_jx_j}\Sigma_{p_jp_j}=\Sigma_{x_jp_j}^2+\hbar^2/4$.
--
--   Define the covariance ellipsoid $\Omega=\{z:\tfrac12 z^T\Sigma^{-1}z\le1\}$. Write $B_R=\{z:|z|\le R\}$ for the closed Euclidean ball and define $c(\Omega)$ to be the supremum of $\pi R^2$ over all $R\ge0$, translations $a\in\mathbb R^{2n}$, and real symplectic matrices $S$ with $a+S(B_R)\subseteq\Omega$. Then
--
--   $$
--   c(\Omega)=\pi\hbar=\frac h2,\qquad h=2\pi\hbar.
--   $$
--
--   Thus a single saturated coordinate uncertainty inequality fixes this symplectic capacity at its smallest physically allowed value. The other coordinate inequalities need not be strict.
--
--   **Formalization Note** The capacity takes values in the extended nonnegative reals, with the displayed finite value embedded in that type. The grouped index type is the disjoint sum of two copies of $\mathrm{Fin}(n)$. Positive definiteness supplies symmetry and guards the inverse. This is a matrix conclusion using condition (8); it makes no density-operator realizability assertion.
-- source:
--   The Unique Pure Gaussian State Determined by the Partial Saturation of the Uncertainty Relations of a Mixed Gaussian State, arXiv:1205.5222v1, PDF p. 7, Section 4, First step (continued on p.8)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P19

noncomputable section

open scoped ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)

namespace QAlgorithms.Papers.Independent.Next46.P19

/-- Section 4, First step, arXiv:1205.5222v1, PDF pp.7–8:
saturation of any coordinate Robertson–Schrodinger inequality forces the
covariance ellipsoid to have capacity h/2 = pi hbar. This is the matrix
formulation using the physicality condition (8), PDF p.4, not an assertion
that a covariance tuple is a density operator. No restriction on the other
modes is imposed; no capacity formula or Williamson data is a hypothesis. -/
theorem saturation_minimal_capacity (n : ℕ) (hn : 0 < n)
    (hbar : ℝ) (hhbar : 0 < hbar) (Sigma : PhaseMatrix n)
    (hSigma : Sigma.PosDef)
    (hphysical : (complexify Sigma +
      (((hbar / 2 : ℝ) : ℂ) * Complex.I) • complexify (sigma n)).PosSemidef)
    (hsaturated : ∃ j : Fin n,
      Sigma (Sum.inl j) (Sum.inl j) * Sigma (Sum.inr j) (Sum.inr j) =
        (Sigma (Sum.inl j) (Sum.inr j)) ^ 2 + hbar ^ 2 / 4) :
    linearSymplecticCapacity (covarianceEllipsoid Sigma) =
      ENNReal.ofReal (Real.pi * hbar) := by sorry

end QAlgorithms.Papers.Independent.Next46.P19

end
