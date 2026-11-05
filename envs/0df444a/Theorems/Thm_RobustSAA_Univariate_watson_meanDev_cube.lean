-- Prove2me | Theorems.Thm_RobustSAA_Univariate_watson_meanDev_cube
-- name    : RobustSAA.Univariate.watson_meanDev_cube
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T20:01:30.907447+00:00
-- url     : https://prove2.me/theorems/2a57bb6f-a46b-41ca-8dab-91d3d0ea9f26
-- title:
--   Watson centring term: $|\frac1N\sum_i F_0(\xi^{(i)})-\frac12|^3\le 8U_N^2$
-- statement:
--   Let $N\ge 1$, let $F_0$ be a distribution on $\mathbb R$ and $\xi^1,\dots,\xi^N$ a sample with order statistics $\xi^{(1)}\le\dots\le\xi^{(N)}$; write $u_i=F_0(\xi^{(i)})\in[0,1]$. With the Cramér–von Mises and Watson statistics of (8),
--
--   $$W_N^2=\frac1{12N^2}+\frac1N\sum_{i=1}^N\Big(\frac{2i-1}{2N}-u_i\Big)^2,\qquad U_N^2=W_N^2-\Big(\frac1N\sum_{i=1}^N u_i-\frac12\Big)^2,$$
--
--   the centring term $m_N=\frac1N\sum_i u_i-\frac12$ satisfies
--
--   $$|m_N|^3\le 8\,U_N^2 .$$
--
--   This lemma replaces the step of the paper's Watson argument (p. 39) that asserts $(\frac1N\sum_i\min\{1,\frac{2i-1}{2N}+D'_N\}-\frac12)^2=O(1/N)$, which fails when $D'_N(F_0)$ is large. Combined with `watson_bound` ($W_N^2-U_N^2=m_N^2$) it gives: $U_N=O(N^{-1/2})$ implies $W_N^2=O(N^{-2/3})=o(N^{-1/2})$, so the CvM bound `ks_sq_le_cvm` forces $D_N\to0$ and the Watson test is uniformly consistent.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.7 (proof of Theorem 5), p. 39 — Watson case; corrected argument (the paper's O(1/N) step fails), via the integral formulation of W_N^2 and U_N^2 (Stephens 1970)

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

namespace RobustSAA.Univariate

open Filter MeasureTheory

theorem watson_meanDev_cube {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) :
    |meanDev F₀ s| ^ 3 ≤ 8 * watsonStat F₀ s ^ 2 := by sorry

end RobustSAA.Univariate
