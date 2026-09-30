-- Prove2me | Theorems.Thm_SzemerediTrotter_Incidence_termination_inequality
-- name    : SzemerediTrotter.Incidence.termination_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T11:07:42.090586+00:00
-- url     : https://prove2.me/theorems/b720e3bd-c9c8-415b-9d8d-a0f2a70e64f6
-- title:
--   Section 3, display on p. 387 — $2^{i/3}(1-2/M)^{4i/3} < 200/((.1)^{1/3}2^{2/3})$ fails for $i \ge 30$
-- statement:
--   Let $M = 10^{10}$. For every natural number $i \ge 30$,
--
--   $$\frac{200}{(0.1)^{1/3}\,2^{2/3}} \le 2^{i/3}\Bigl(1-\frac{2}{M}\Bigr)^{4i/3}.$$
--
--   Equivalently, the inequality $2^{i/3}(1-2/M)^{4i/3} < 200/((.1)^{1/3}2^{2/3})$ obtained on p. 387 of Szemerédi and Trotter fails whenever $i \ge 30$. In the proof of Theorem 1 this shows that the inductive construction of the point sets $\mathcal P_i$ terminates after fewer than $30$ steps.
--
--   **Formalization Note** $M = 10^{10}$ is written out in the statement. The exponents $i/3$ and $4i/3$ are real numbers (the natural number $i$ is cast to $\mathbb R$ before dividing), and the powers are `Real.rpow`; the bases $2$, $0.1$ and $1 - 2/M$ are positive.
-- source:
--   Szemerédi, Trotter, Extremal Problems in Discrete Geometry, Combinatorica 3 (1983), p. 387, Section 3, display on p. 387 (with M = 10¹⁰ set on p. 386)

import Mathlib

namespace SzemerediTrotter.Incidence

/-- Section 3, display on p. 387, with `M = 10¹⁰` (p. 386): the inequality
`2^{i/3}(1 − 2/M)^{4i/3} < 200/((.1)^{1/3} 2^{2/3})` fails for every `i ≥ 30`. -/
theorem termination_inequality :
    ∀ i : ℕ, 30 ≤ i →
      (200 : ℝ) / ((0.1 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ))
        ≤ (2 : ℝ) ^ ((i : ℝ) / 3) * (1 - 2 / (10 : ℝ) ^ 10) ^ (4 * (i : ℝ) / 3) := by sorry

end SzemerediTrotter.Incidence
