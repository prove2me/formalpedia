-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_dirichlet_achievability
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.dirichlet_achievability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:17:46.826006+00:00
-- url     : https://prove2.me/theorems/949d202b-6e19-47f7-aaab-3279d713cde1
-- title:
--   Theorem 1.4: Dirichlet-eigenvalue achievability
-- statement:
--   Fix $d\ge1$. In the affine hyperplane $\sum_i x_i=1$, equip the ordered probability simplex $OS_{d-1}=\{x_1\ge\cdots\ge x_d\ge0,\ \sum_i x_i=1\}$ with its intrinsic Euclidean metric. Let $\lambda_1$ be the lowest Dirichlet-Laplacian eigenvalue on its relative interior, equivalently its $H_0^1$ Rayleigh infimum. There are $C_d>0$ and $N_0\ge1$ such that
--   $$F_d^*(N)\ge1-\frac{\lambda_1(OS_{d-1})}{dN^2}-\frac{C_d}{N^3}\qquad(N\ge N_0).$$
--   This is an achievability bound, without asserting an optimal limiting coefficient.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 6, Theorem 1.4: Dirichlet-eigenvalue achievability

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Theorem 1.4, PDF p.6: Dirichlet achievability in the intrinsic sum-one hyperplane.
Corrected printed OS_d to OS_(d-1), matching the definition on the same page and pp.45–46. -/
theorem dirichlet_achievability (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0,
      1 - dirichletFirst d / ((d : ℝ)*(N : ℝ)^2) - C/(N : ℝ)^3 ≤
        pbtOptimalFidelity d N := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
