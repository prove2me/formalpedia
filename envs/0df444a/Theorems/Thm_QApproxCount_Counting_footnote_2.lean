-- Prove2me | Theorems.Thm_QApproxCount_Counting_footnote_2
-- name    : QApproxCount.Counting.footnote_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:10:41.098989+00:00
-- url     : https://prove2.me/theorems/b0697cda-5ab2-4ba6-8237-61297958aae1
-- title:
--   Footnote 2 — 1 − ε ≤ sin²(θ(1 + ε/5))/sin²(θ) ≤ 1 + ε for 0 < θ ≤ 0.002 and 0 < ε < 1
-- statement:
--   For $0<\theta\le0.002$ and $0<\varepsilon<1$,
--   $$1-\varepsilon\ \le\ \frac{\sin^2\!\big(\theta(1+\varepsilon/5)\big)}{\sin^2\theta}\ \le\ 1+\varepsilon .$$
--
--   This converts a $(1+\varepsilon/5)$-factor estimate of the angle $\theta$ into a $(1\pm\varepsilon)$-factor estimate of $K=N'\sin^2\theta$.
--
--   **Formalization Note** The footnote states the inequality without a range for $\theta$. The range $0<\theta\le0.002$ is the one in which the algorithm uses it ($\theta\le0.001$ after padding, and $\theta_{\max}\le0.002$).
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, p. 7, footnote 2

import Mathlib

namespace QApproxCount.Counting

/-- Footnote 2, p. 7: for `0 < θ ≤ 0.002` and `0 < ε < 1`,
`1 - ε ≤ sin²(θ(1 + ε/5)) / sin²(θ) ≤ 1 + ε`. -/
theorem footnote_2 (θ ε : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 0.002) (hε : 0 < ε) (hε1 : ε < 1) :
    1 - ε ≤ Real.sin (θ * (1 + ε / 5)) ^ 2 / Real.sin θ ^ 2 ∧
      Real.sin (θ * (1 + ε / 5)) ^ 2 / Real.sin θ ^ 2 ≤ 1 + ε := by sorry

end QApproxCount.Counting
