-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P02_covariance_closed_convex
-- name    : QAlgorithms.Papers.Independent.Frontier30.P02.covariance_closed_convex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:10:27.21185+00:00
-- url     : https://prove2.me/theorems/6167cb6c-0101-4bc8-b2e2-2b1dec651cfe
-- title:
--   The Gaussian covariance set is closed and convex
-- statement:
--   Let $n$ be a positive integer and put $J=\begin{bmatrix}0&-I_n\\I_n&0\end{bmatrix}$. Let $K_n$ be the set of real symmetric $2n\times2n$ matrices $S$ such that the complex Hermitian matrix $2S-iJ$ is positive semidefinite. In the usual topology on the space of all real $2n\times2n$ matrices,
--
--   $$
--   K_n\text{ is closed and convex}.
--   $$
--
--   This describes the geometry of the covariance matrices used throughout the paper.
-- source:
--   The Symmetry Group of Gaussian States in $L^2 (\mathbb{R}^n)$, arXiv:1101.5041v1, PDF p. 2, §1, following (1.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02

noncomputable section

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify)

namespace QAlgorithms.Papers.Independent.Frontier30.P02

/-- K_n is closed and convex in the space of all real matrices.
Source: arXiv:1101.5041v1, PDF p.2, the sentence following (1.3). -/
theorem covariance_closed_convex (n : ℕ) (hn : 0 < n) :
    IsClosed (covarianceSet n) ∧ Convex ℝ (covarianceSet n) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P02

end
