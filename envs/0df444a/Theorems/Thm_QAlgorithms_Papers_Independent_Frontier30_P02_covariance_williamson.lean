-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P02_covariance_williamson
-- name    : QAlgorithms.Papers.Independent.Frontier30.P02.covariance_williamson
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:11:14.102906+00:00
-- url     : https://prove2.me/theorems/0fbb1fd4-abbe-43cb-b65e-03ed99605736
-- title:
--   Williamson normal form, uniqueness, and determinant bound
-- statement:
--   Let $n>0$, $J=\begin{bmatrix}0&-I_n\\I_n&0\end{bmatrix}$, and $K_n=\{S=S^T\in M_{2n}(\mathbb R):2S-iJ\ge0\}$. The inequality is in the Hermitian Loewner order. For any real $2n\times2n$ matrix $S$, membership in $K_n$ is equivalent to existence of a unique ordered vector $d_1\ge\cdots\ge d_n\ge1/2$ for which there is a real symplectic matrix $M$ satisfying
--
--   $$
--   S=M^T\begin{bmatrix}D&0\\0&D\end{bmatrix}M,\qquad D=\operatorname{diag}(d_1,\ldots,d_n),\qquad M^TJM=J.
--   $$
--
--   Every member $S$ is positive definite. For every such representation,
--
--   $$
--   \det S=\prod_{j=1}^n d_j^2\ge4^{-n}.
--   $$
--
--   These parameters are the ordered symplectic eigenvalues; uniqueness is asserted for $D$, not for $M$.
-- source:
--   The Symmetry Group of Gaussian States in $L^2 (\mathbb{R}^n)$, arXiv:1101.5041v1, PDF p. 8, Theorem 2, (3.5)–(3.6), pp.8–9

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02

noncomputable section

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify)

namespace QAlgorithms.Papers.Independent.Frontier30.P02

/-- Theorem 2, arXiv:1101.5041v1, PDF pp.8–9, (3.5)–(3.6), including
positive definiteness derived on p.9 and uniqueness in the final sentence.
The printed product's inconsistent dummy index is read as a product over j. -/
theorem covariance_williamson {n : ℕ} (hn : 0 < n) (S : PhaseMatrix n) :
    (S ∈ covarianceSet n ↔
      ∃! d : Fin n → ℝ, ∃ M : PhaseMatrix n, WilliamsonData S d M) ∧
    (S ∈ covarianceSet n → S.PosDef ∧ (1 / 4 : ℝ) ^ n ≤ S.det) ∧
    (∀ (d : Fin n → ℝ) (M : PhaseMatrix n), WilliamsonData S d M →
      S.det = ∏ j : Fin n, (d j) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P02

end
