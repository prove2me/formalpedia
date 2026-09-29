-- Prove2me | Theorems.Thm_Polynomial_log_norm_coeff_le_logMahlerMeasure_add
-- name    : Polynomial.log_norm_coeff_le_logMahlerMeasure_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/829fbd3a-2b0f-58c5-a3d8-a69d6d682bad
-- title:
--   Coefficient bound by logarithmic Mahler measure
-- statement:
--   Let $p \in \mathbb{C}[X]$ be a polynomial and let $k$ be a natural number such that the $k$-th coefficient of $p$ is non-zero. Then $$\log \lVert p_k\rVert \le m(p) + (\deg p)\log 2,$$ where $p_k$ denotes `p.coeff k`, $\lVert\cdot\rVert$ is the complex absolute value, $m(p)$ is `Polynomial.logMahlerMeasure`, the logarithmic Mahler measure $\frac{1}{2\pi}\int_0^{2\pi}\log\lvert p(e^{i\theta})\rvert\,d\theta$, and $\deg p$ is the natural-number degree `p.natDegree`, coerced to a real number. No non-vanishing or normalisation assumption on $p$ beyond $p_k \ne 0$ is imposed; this hypothesis in particular forces $p \ne 0$ and $k \le \deg p$, and it is what makes the left-hand side a genuine logarithm of a positive real (Lean's $\log 0 = 0$ would otherwise break the inequality, the right-hand side being possibly negative).
--
--   This is Mahler's coefficient inequality in logarithmic form: the logarithmic height of a single coefficient exceeds the logarithmic Mahler measure by at most $\log 2$ per unit of degree. It is the one-variable case feeding the multivariate statement [`MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add`](thm.html#MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add) and the integrability statement [`MvPolynomial.integrableOn_log_norm_eval_circleMap`](thm.html#MvPolynomial.integrableOn_log_norm_eval_circleMap), and it is used in the height estimate [`AlgebraicCurve.absLogHeight_coeff_le_sum_roots`](thm.html#AlgebraicCurve.absLogHeight_coeff_le_sum_roots).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_log_norm_coeff_le_logMahlerMeasure_add.lean

import Mathlib.Analysis.Polynomial.MahlerMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Polynomial.log_norm_coeff_le_logMahlerMeasure_add {p : Polynomial ℂ} {k : ℕ} (hk : p.coeff k ≠ 0) :
    Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure + p.natDegree * Real.log 2 := by sorry
