-- Prove2me | Theorems.Thm_SpikedWishart_LastPassage_eq_310
-- name    : SpikedWishart.LastPassage.eq_310
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:45.302986+00:00
-- url     : https://prove2.me/theorems/3e781205-8788-4ccf-9f48-3ef66a3bef65
-- title:
--   (310), pp. 1692–1693 — P(G(N, M) ≤ n) = Π(1 − x_iy_j) · Σ_{λ₁ ≤ n} s_λ(x)s_λ(y)
-- statement:
--   Let $N, M \ge 1$, let $x_1,\ldots,x_N$ and $y_1,\ldots,y_M$ lie in $[0,1)$, and attach to each site $(i,j)$ of the $N\times M$ grid an independent geometric random variable $Y(i,j)$ with
--   $$\mathbb P(Y(i,j) = k) = (1-x_iy_j)(x_iy_j)^k, \qquad k = 0, 1, 2, \ldots$$
--   Let $G(N,M)$ be the last passage time from $(1,1)$ to $(N,M)$ for these weights, as in (306). Then for every integer $n \ge 0$,
--   $$\mathbb P\big(G(N,M) \le n\big) = \prod_{i=1}^N\prod_{j=1}^M (1-x_iy_j) \cdot \sum_{\lambda:\ \lambda_1 \le n} s_\lambda(x)\, s_\lambda(y),$$
--   the sum over all partitions $\lambda$ whose first part $\lambda_1$ is at most $n$, with $s_\lambda$ the Schur function.
--
--   This is the Robinson–Schensted–Knuth formula for geometric last passage percolation; the exponential law (307) is obtained from it by a scaling limit.
--
--   **Formalization Note** The paper's variables are infinite sequences with $x_i = 0$ for $i > N$ and $y_j = 0$ for $j > M$; finitely many variables are exactly that case. The first part $\lambda_1$ is the length of the first row of the Young diagram. The paper's bracket writes $\mathbb P(X(i,j) = k)$ for the geometric variable $Y(i,j)$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1692–1693, (310)

import Mathlib
import Definitions.Def_SpikedWishart_LastPassage_LPP
import Definitions.Def_SpikedWishart_LastPassage_Schur

namespace SpikedWishart.LastPassage

open MeasureTheory

/-- (310): for independent geometric site variables `Y(i, j)` with parameter `x_i y_j`, the last
passage time `G(N, M)` satisfies
`P(G(N, M) ≤ n) = ∏_{i,j} (1 - x_i y_j) · Σ_{μ : μ₁ ≤ n} s_μ(x) s_μ(y)`. -/
theorem eq_310 {N M : ℕ} [NeZero N] [NeZero M] (x : Fin N → ℝ) (y : Fin M → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) (hy0 : ∀ j, 0 ≤ y j) (hy1 : ∀ j, y j < 1)
    (n : ℕ) :
    (geomLaw x y).real {Y | L (fun i j => (Y i j : ℝ)) ≤ n} =
      (∏ i, ∏ j, (1 - x i * y j)) *
        ∑' μ : {μ : YoungDiagram // μ.rowLen 0 ≤ n}, schur x μ.1 * schur y μ.1 := by sorry

end SpikedWishart.LastPassage
