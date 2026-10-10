-- Prove2me | Theorems.Thm_RandomListsMatching_GeneralRates_per_advertiser_bound
-- name    : RandomListsMatching.GeneralRates.per_advertiser_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:57.05132+00:00
-- url     : https://prove2.me/theorems/cd547f23-1392-4c60-8282-27ffcb5419d7
-- title:
--   §5.4, pp. 15–16 — the per-advertiser ratio of Theorem 3 is at least 0.706 when f − s ≤ 1 − ln 2
-- statement:
--   Let $h$, $g$ be the functions of Claim 2,
--   $$
--   h(y,x)=\begin{cases}\dfrac{y}{y-x}\,\bigl(e^{-x}-e^{-y}\bigr), & x\neq y,\\[4pt] y\,e^{-y}, & x=y,\end{cases}\qquad g(y,x)=h(y,0)-h(y,x).
--   $$
--   Let $0 < f \le 1$, and let $x_1, \dots, x_k$ and $y_1, \dots, y_k$ ($k \ge 0$) be reals with
--   1. $0 \le x_j \le y_j \le 1$ for every $j$;
--   2. $s = \sum_j x_j \le f$;
--   3. $f - s \le 1 - \ln 2$.
--
--   Then
--   $$
--   \frac{1 - e^{-f} + \frac1e \sum_{j} g(f, x_j) - \frac1{2e}\Bigl(\sum_j g(y_j, x_j)\Bigr)^2 + \frac1{2e}\sum_j g(f, x_j)^2}{f} \;\ge\; 0.706 .
--   $$
--
--   In Jaillet and Lu's proof of Theorem 3 (online stochastic matching with general arrival rates), $f = f_a \le 1$ is the LP flow into an advertiser $a$, $j$ ranges over its neighbours $a_1 \in A^*_a$ including the dummy $a_d$, $x_j = m_{a,a_1} = m_{a_1,a}$ is the expected number of lists $\langle a, a_1\rangle$ and $y_j = f_{a_1}$. The left-hand side is the ratio inside $\min_{a \in A}$ on p. 15, and the paper's chain gives $\sum_a p_a / \sum_a f_a \ge \min_a(\cdot)$; the bound $0.706$ on each ratio is therefore exactly the analytic content of Theorem 3's $\sum_a p_a \ge 0.706 \sum_a f_a$.
--
--   **Formalization Note** The paper's constraint is $f - s \le (1 - \ln 2) + 1/n$ with $n \ge 100$ (p. 16); with the $1/n$ kept the inequality fails at $n = 100$ ($k = 1$, $f = 1$, $x_1 = \ln 2 - 0.01$, $y_1 = 1$ gives $\approx 0.70543$), so the statement takes the $n \to \infty$ limit $f - s \le 1 - \ln 2$, the regime of Theorem 3. Advertisers with $f_a = 0$ are excluded ($0/0$ in the paper; $0$ in Lean). The hypotheses $x_j \le y_j \le 1$ are the paper's $m_{a_1,a} \le s_{a_1} \le f_{a_1} \le 1$. $k = 0$ is allowed. Theorem 3 itself, Claim 2 and the bound on $p_a$ rest on asymptotic approximations and are not part of this statement.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 15, third line of the chain (≥ min_{a∈A} […]/f_a), with Claim 4, p. 16, and "Theorem 3 follows from Claim 4", p. 16; limit form of the constraint

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

namespace RandomListsMatching.GeneralRates

theorem per_advertiser_bound (f : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) {k : ℕ} (x y : Fin k → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hxy : ∀ j, x j ≤ y j) (hy : ∀ j, y j ≤ 1) (hs : ∑ j, x j ≤ f)
    (hgap : f - ∑ j, x j ≤ 1 - Real.log 2) :
    (0.706 : ℝ) ≤ bracket f x y / f := by sorry

end RandomListsMatching.GeneralRates
