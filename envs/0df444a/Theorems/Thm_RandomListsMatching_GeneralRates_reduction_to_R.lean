-- Prove2me | Theorems.Thm_RandomListsMatching_GeneralRates_reduction_to_R
-- name    : RandomListsMatching.GeneralRates.reduction_to_R
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:33.28018+00:00
-- url     : https://prove2.me/theorems/b646ef8b-97ce-469b-b586-383806cb3caa
-- title:
--   §5.4, p. 15 last display — the per-advertiser ratio is at least R(f_a, β_a, s_a)
-- statement:
--   Let $g$, the bracket $B$ and $R$ be as in the mission's definitions. Let $0 < f \le 1$, and let $x_1, \dots, x_k$, $y_1, \dots, y_k$ be reals with $0 \le x_j \le y_j \le 1$ for every $j$ and $s = \sum_j x_j \le f$. Let $j_0$ be an index at which $x$ attains its maximum $\beta = x_{j_0}$, and suppose $\beta > 0$. Then
--   $$
--   \frac1f\Bigl(1 - e^{-f} + \frac1e \sum_{j} g(f, x_j) - \frac1{2e}\Bigl(\sum_j g(y_j, x_j)\Bigr)^2 + \frac1{2e}\sum_j g(f, x_j)^2\Bigr) \;\ge\; R(f, \beta, s).
--   $$
--
--   This is the last display of p. 15 of Jaillet and Lu (with $f = f_a$, $x_j = m_{a,a_1}$, $y_j = f_{a_1}$, $\beta = \beta_a$, $s = s_a$). It combines the two preceding displays with $\sum_j g(f, x_j)^2 \ge g(f, \beta)^2$ and reduces the per-advertiser ratio to the three-variable function $R$ bounded in Claim 4.
--
--   **Formalization Note** The positivity of $f$ and of $\beta$ makes the divisions in the bracket ratio and in $R$ genuine; in the paper an advertiser with $\beta_a = 0$ has $s_a = 0$ and is covered by the mission's goal without $R$.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 15, sentence "Then, we have Σ g(f_a, m_{a,a1})² ≥ g(f_a, β_a)²" and the last display (≥ … ≜ R(f_a, β_a, s_a))

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

namespace RandomListsMatching.GeneralRates

theorem reduction_to_R (f : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) {k : ℕ} (x y : Fin k → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hxy : ∀ j, x j ≤ y j) (hy : ∀ j, y j ≤ 1) (hs : ∑ j, x j ≤ f)
    (j₀ : Fin k) (hmax : ∀ j, x j ≤ x j₀) (hβ : 0 < x j₀) :
    R f (x j₀) (∑ j, x j) ≤ bracket f x y / f := by sorry

end RandomListsMatching.GeneralRates
