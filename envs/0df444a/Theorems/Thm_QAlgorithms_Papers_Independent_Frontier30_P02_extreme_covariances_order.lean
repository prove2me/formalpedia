-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P02_extreme_covariances_order
-- name    : QAlgorithms.Papers.Independent.Frontier30.P02.extreme_covariances_order
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:12:49.721763+00:00
-- url     : https://prove2.me/theorems/752a1974-c836-4325-b46b-d464f0a2d141
-- title:
--   Comparable extreme Gaussian covariances coincide
-- statement:
--   Let $n>0$, $J=\begin{bmatrix}0&-I_n\\I_n&0\end{bmatrix}$, and $K_n=\{S=S^T\in M_{2n}(\mathbb R):2S-iJ\ge0\}$. Suppose that $S_1$ and $S_2$ are extreme points of $K_n$ and $S_1-S_2$ is positive semidefinite. Then
--
--   $$
--   S_1=S_2.
--   $$
--
--   Thus two extreme Gaussian covariance matrices cannot be distinct and comparable in the Loewner order.
-- source:
--   The Symmetry Group of Gaussian States in $L^2 (\mathbb{R}^n)$, arXiv:1101.5041v1, PDF p. 12, Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02

noncomputable section

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify)

namespace QAlgorithms.Papers.Independent.Frontier30.P02

/-- Corollary 1, arXiv:1101.5041v1, PDF p.12.
The inequality S1 >= S2 is the Loewner inequality, encoded by positivity
of S1 - S2, with both matrices required to be actual extreme points. -/
theorem extreme_covariances_order {n : ℕ} (hn : 0 < n) (S1 S2 : PhaseMatrix n)
    (h1 : S1 ∈ Set.extremePoints ℝ (covarianceSet n))
    (h2 : S2 ∈ Set.extremePoints ℝ (covarianceSet n))
    (horder : (S1 - S2).PosSemidef) : S1 = S2 := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P02

end
