-- Prove2me | Theorems.Thm_RobustSAA_Discrete_g_tv_bound
-- name    : RobustSAA.Discrete.g_tv_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:38.752915+00:00
-- url     : https://prove2.me/theorems/55059fe8-d149-49cc-b3f9-ec2577a9f152
-- title:
--   §10.6, p. 38 — Pinsker bound for the G statistic
-- statement:
--   For a positive sample size $N$, let $\widehat p_N$ be the empirical probability vector of a sample and let $p_0$ be any hypothetical probability vector on the same known finite support. Then
--
--   $$
--   d_{\mathrm{TV}}(\widehat p_N,p_0)\leq\frac{G_N(F_0)}{2},
--   \qquad\text{equivalently}\qquad
--    d_{\mathrm{TV}}(\widehat p_N,p_0)^2\leq\frac12\sum_j\widehat p_N(j)\log\frac{\widehat p_N(j)}{p_0(j)}.
--   $$
--
--   This Pinsker estimate controls the G-test confidence region by the same total-variation metric.
--
--   **Formalization Note** $N>0$ makes the empirical frequencies a probability vector. The paper's displayed middle expression accidentally repeats the sum over $j$; the Lean statement uses the single sum defined for $G_N$ on p. 8. An empirical positive mass against $p_0(j)=0$ yields $+\infty$.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.6, p. 38, third display; corrected repeated sum

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting

namespace RobustSAA.Discrete

open MeasureTheory

theorem g_tv_bound {n N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure (Fin n))
    (s : Fin N → Fin n) :
    ((dTV (phat s) (pvec F₀)) ^ 2 : EReal) ≤
      (∑ j : Fin n, gTerm F₀ s j) / 2 := by sorry

end RobustSAA.Discrete
