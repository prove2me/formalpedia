-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P11_generalizedWilliamson
-- name    : QAlgorithms.Papers.Independent.Frontier18.P11.generalizedWilliamson
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:34:48.682989+00:00
-- url     : https://prove2.me/theorems/8bdef61d-25d8-490a-8aa1-c455ee4345e3
-- title:
--   Generalized Williamson normal form, including singular covariance
-- statement:
--   Let $s\ge0$, and let $\mu,\Delta_K$ be real $2s\times2s$ matrices such that $\mu^t=\mu$, $\Delta_K^t=-\Delta_K$, and the complex Hermitian matrix $\mu-\tfrac{i}{2}\Delta_K$ is positive semidefinite. There exist nonnegative integers $q,c,z$, real numbers $\nu_j\ge\tfrac12$ for $1\le j\le q$, and a real invertible matrix $T$ such that
--
--   $$
--   2q=\operatorname{rank}\Delta_K,\qquad
--   2q+c=\operatorname{rank}\mu,\qquad
--   2q+c+z=2s,
--   $$
--
--   and
--
--   $$
--   T^t\mu T=\operatorname{diag}(\nu_1 I_2,\ldots,\nu_q I_2,\tfrac12 I_c,0_z),\qquad
--   T^t\Delta_K T=\operatorname{diag}(J,\ldots,J,0_c,0_z),\quad
--   J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
--   $$
--
--   Thus the last two block dimensions are exactly $\operatorname{rank}\mu-\operatorname{rank}\Delta_K$ and $2s-\operatorname{rank}\mu$. No nonsingularity assumption on either input matrix is imposed. This normal form separates quantum, positive-variance classical, and zero-variance directions.
--
--   **Formalization Note** The existential sequence $\nu:\mathbb N\to\mathbb R$ is used only at its first $q$ entries. Dimension identities avoid truncated natural subtraction. Empty matrices are allowed at $s=0$.
-- source:
--   On the Choi-Jamiolkowski Correspondence in Infinite Dimensions, arXiv:1004.0196v3, PDF p. 14, Lemma 3: generalized Williamson normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P11

noncomputable section

open scoped TensorProduct ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P11

/-- Lemma 3, PDF pp.14–15, (30)–(31), including the continuation nu_j >= 1/2.
No invertibility of mu or Delta is assumed. Counts q,c,z are nonnegative,
2q=rank Delta, 2q+c=rank mu, and 2q+c+z=2s; thus c and z are precisely the
printed rank differences, without natural subtraction hiding an invalid case.
The unused tail of nu has no mathematical content. The empty-mode case is
included: all matrices are empty and det T=1. -/
theorem generalizedWilliamson (s : ℕ)
    (mu Delta : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ)
    (hmu : mu.transpose = mu) (hDelta : Delta.transpose = -Delta)
    (hpositive :
      (complexMatrix mu - (Complex.I / 2) • complexMatrix Delta).PosSemidef) :
    ∃ (q c z : ℕ) (nu : ℕ → ℝ)
        (T : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ),
      2 * q = Delta.rank ∧
      2 * q + c = mu.rank ∧
      2 * q + c + z = 2 * s ∧
      (∀ j < q, (1 / 2 : ℝ) ≤ nu j) ∧
      T.det ≠ 0 ∧
      T.transpose * mu * T = normalCovariance (2 * s) q c nu ∧
      T.transpose * Delta * T = normalCommutator (2 * s) q := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P11

end
