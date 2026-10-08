-- Prove2me | Theorems.Thm_SpikedWishart_LastPassage_eq_311
-- name    : SpikedWishart.LastPassage.eq_311
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:40.806846+00:00
-- url     : https://prove2.me/theorems/9d41cdc6-c58b-4f17-b3d6-e812aec2aca4
-- title:
--   (311), p. 1693 — Cauchy identity Σ_λ s_λ(x)s_λ(y) = Π_{i,j}(1 − x_iy_j)⁻¹
-- statement:
--   Let $x_1,\ldots,x_n \ge 0$ and $y_1,\ldots,y_m \ge 0$ satisfy $x_iy_j < 1$ for all $i, j$, and let $s_\lambda$ denote the Schur function. Then the series over all partitions $\lambda$ converges and
--   $$\sum_\lambda s_\lambda(x)\, s_\lambda(y) = \prod_{i=1}^n \prod_{j=1}^m \frac{1}{1-x_iy_j}.$$
--
--   This is the Cauchy identity; it gives the normalisation constant in the geometric last passage formula (310).
--
--   **Formalization Note** The page prints the right-hand side as $\prod_{i,j}(1-x_iy_j)$, without the exponent $-1$; this is a printed slip (with one variable on each side, $x_1 = y_1 = q$, the left side is $\sum_k q^{2k} = 1/(1-q^2)$), and (310) uses the correct normalisation. The true identity is stated. Finitely many variables are the paper's infinite sequences with $x_i = 0$, $y_j = 0$ beyond $n$, $m$. Convergence is asserted as `HasSum` over all Young diagrams.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1693, (311)

import Mathlib
import Definitions.Def_SpikedWishart_LastPassage_Schur

namespace SpikedWishart.LastPassage

/-- (311), the Cauchy identity: `Σ_μ s_μ(x) s_μ(y) = ∏_{i,j} (1 - x_i y_j)⁻¹`, the sum over all
partitions `μ`, for nonnegative variables with `x_i y_j < 1`. -/
theorem eq_311 {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) (hxy : ∀ i j, x i * y j < 1) :
    HasSum (fun μ : YoungDiagram => schur x μ * schur y μ) (∏ i, ∏ j, (1 - x i * y j)⁻¹) := by sorry

end SpikedWishart.LastPassage
