-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P02_covariance_grams_extreme
-- name    : QAlgorithms.Papers.Independent.Frontier30.P02.covariance_grams_extreme
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:12:16.70904+00:00
-- url     : https://prove2.me/theorems/f1fbd80e-fd72-4afd-957a-6ac29ebbcd71
-- title:
--   Two symplectic Gram matrices and all extreme covariances
-- statement:
--   Let $n>0$ and let $S$ be a real positive definite matrix of order $2n$. Set $J=\begin{bmatrix}0&-I_n\\I_n&0\end{bmatrix}$ and $K_n=\{A=A^T\in M_{2n}(\mathbb R):2A-iJ\ge0\}$, using Hermitian positivity. Write $\operatorname{Sp}(2n,\mathbb R)=\{L:L^TJL=J\}$. Then
--
--   $$
--   S\in K_n\quad\Longleftrightarrow\quad\exists L,M\in\operatorname{Sp}(2n,\mathbb R),\quad S=\frac14(L^TL+M^TM).
--   $$
--
--   Moreover, for the actual extreme points of this convex set,
--
--   $$
--   S\in\operatorname{Ext}(K_n)\quad\Longleftrightarrow\quad\exists L\in\operatorname{Sp}(2n,\mathbb R),\quad S=\frac12L^TL.
--   $$
--
--   This identifies every extreme covariance and expresses every covariance as a midpoint of two of them.
-- source:
--   The Symmetry Group of Gaussian States in $L^2 (\mathbb{R}^n)$, arXiv:1101.5041v1, PDF p. 10, Theorem 3, pp.10–12

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02

noncomputable section

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify)

namespace QAlgorithms.Papers.Independent.Frontier30.P02

/-- Theorem 3, arXiv:1101.5041v1, PDF pp.10–12: both equivalences.
The factor 1/4 is the printed theorem and proof; the abstract and introduction
instead print 1/2, which fails for the vacuum covariance I/2. -/
theorem covariance_grams_extreme {n : ℕ} (hn : 0 < n) (S : PhaseMatrix n)
    (hS : S.PosDef) :
    (S ∈ covarianceSet n ↔
      ∃ L M : PhaseMatrix n, IsSymplectic L ∧ IsSymplectic M ∧
        S = (1 / 4 : ℝ) • (L.transpose * L + M.transpose * M)) ∧
    (S ∈ Set.extremePoints ℝ (covarianceSet n) ↔
      ∃ L : PhaseMatrix n, IsSymplectic L ∧
        S = (1 / 2 : ℝ) • (L.transpose * L)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P02

end
