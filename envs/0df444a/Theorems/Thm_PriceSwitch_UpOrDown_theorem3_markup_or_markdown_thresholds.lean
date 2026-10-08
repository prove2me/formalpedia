-- Prove2me | Theorems.Thm_PriceSwitch_UpOrDown_theorem3_markup_or_markdown_thresholds
-- name    : PriceSwitch.UpOrDown.theorem3_markup_or_markdown_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:07.173743+00:00
-- url     : https://prove2.me/theorems/b9c86dde-6f1a-4f47-a66d-0f9bd560cc97
-- title:
--   Theorem 3, pp. 1385–1386 — one markdown or markup: strictly increasing thresholds x_n < t¹_n < t_n < t²_n < z_n with J(n,t) = V(n,t)
-- statement:
--   Sales start at price $p$ with Poisson demand of intensity $\lambda$, and once during the horizon the price may be changed either down to $p_1$ or up to $p_2$, where
--
--   $$
--   p_1 < p < p_2, \qquad \lambda_1 > \lambda > \lambda_2, \qquad r_1 = p_1\lambda_1 > r = p\lambda > r_2 = p_2\lambda_2,
--   $$
--
--   all positive. Let $J^i(n,t;0)$ be the revenue of switching at once to $p_i$, $J(n,t;0) = \max\{J^1(n,t;0), J^2(n,t;0)\}$, $J(n,t;t)$ the revenue of keeping $p$, and $J(n,t)$ the optimal expected revenue over all non-anticipating switching times. Let $G^i(n,t) = r - r_i - p_i(\lambda - \lambda_i)P(N_i(t) \ge n)$, $\Delta^i(n,t) = J(n,t;t) - J^i(n,t;0)$, $\Delta(n,t) = J^1(n,t;0) - J^2(n,t;0)$, $t^i_n = \inf\{t > 0 : \Delta^i(n,t) = 0\}$ and $t_n = \inf\{t > 0 : \Delta(n,t) = 0\}$.
--
--   **Assumption** (as on p. 1385): $t^1_n < t_n < t^2_n$ for every $n \ge 1$.
--
--   **Theorem.** There exist two strictly increasing sequences $(x_n)_{n\ge1}$ and $(z_n)_{n \ge 1}$ of time thresholds with
--
--   $$
--   x_n < t^1_n < t_n < t^2_n < z_n,
--   $$
--
--   such that $J(n,t) = V(n,t)$ for all $n$ and $t \ge 0$, where $V(0,t) = 0$ and, for $n \ge 1$,
--
--   $$
--   V(n,t) = \begin{cases} J(n,t;0) + F(n,t) & \text{if } x_n \le t \le z_n, \\ J(n,t;0) & \text{otherwise,} \end{cases}
--   \qquad
--   F(n,t) = \begin{cases} H^1(n,t) & \text{if } x_n \le t \le t_n, \\ H^2(n,t) & \text{if } t_n \le t \le z_n, \\ 0 & \text{otherwise,} \end{cases}
--   $$
--
--   with $F(0,t) = 0$. Here, with $L^i(n,t) = G^i(n,t) + \lambda[V(n-1,t) - J^i(n-1,t;0)]$:
--   1. $H^1(n,\cdot)$ solves $\partial H/\partial t = -\lambda H + L^1(n,t)$ with $H(n,x_n) = 0$;
--   2. $H^2(n,\cdot)$ solves $\partial H/\partial t = -\lambda H + L^2(n,t)$ with $H(n,t_n) = H^1(n,t_n)$;
--   3. $x_n = \inf\{t \ge 0 : L^1(n,t) = 0\}$ and $z_n = \inf\{t \ge t_n : H^2(n,t) \le 0\}$, both sets being nonempty.
--
--   In words: with $n$ items left, it is optimal to mark down to $p_1$ immediately when the time-to-go is below $x_n$, to mark up to $p_2$ immediately when it is above $z_n$, and in between to keep $p$, the stopping value exceeding the switch-at-once revenue by $F(n,t)$. This is the main result of §5.
--
--   **Formalization Note** The sequences, $F$, $H^1$, $H^2$ and $V$ are existentially quantified; $V$ is tied to $F$ and $F$ to $H^1, H^2$ by explicit equations, each $H^i(n,\cdot)$ is pinned by its linear ODE (imposed at every $t > 0$) and its boundary value, and $x_n, z_n$ by their defining infima, so the existential determines the paper's objects; $V$ is a separate witness only because $L^i(n,\cdot)$ reads $V(n-1,\cdot)$. At $n = 1$, $V(0,t) - J^i(0,t;0) = 0$, as the page's "$J(n,t;0) \doteq 0$ for $n \le 0$" gives. The page's closed intervals overlap at $t_n$, where the two branches of $F$ agree by the boundary condition of $H^2$; the formalization keeps the page's inequalities with the first branch taking precedence. The page's assumption $t^1_n < t_n < t^2_n$ is a hypothesis, as on the page; the three infima are Lean `sInf`s, whose sets are nonempty by Lemma 3. In §5 the low price is $p_1$ and the high price $p_2$, with initial price $p$ (in §4, $p_1$ was the initial price). The demand at $p$ is the referenced exponential-interarrival counting process (`IsExpInterarrivals P lam T`); `IsProbabilityMeasure P` is redundant given it. The sum of independent Poisson counts in $J^i(n,t;s)$ is written through its Poisson law.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Theorem 3, pp. 1385–1386 (assumption t¹_n < t_n < t²_n, p. 1385; proof: Appendix, pp. 1388–1390)

import Mathlib
import Definitions.Def_PriceSwitch_UpOrDown_ThreePrice

namespace PriceSwitch.UpOrDown

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

/-- Feng–Gallego (1995), Theorem 3, pp. 1385–1386: with one markdown (to `p₁`) or one markup (to `p₂`)
allowed from the initial price `p`, and under the page's assumption `t¹_n < t_n < t²_n`, there are strictly
increasing thresholds `x_n < t¹_n < t_n < t²_n < z_n` with `J(n, t) = V(n, t)`. -/
theorem theorem3_markup_or_markdown_thresholds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ → Ω → ℝ)
    (p₁ lam₁ p lam p₂ lam₂ : ℝ)
    (h3 : IsThreePrice p₁ lam₁ p lam p₂ lam₂)
    (hT : IsExpInterarrivals P lam T)
    (hassume : ∀ n : ℕ, 1 ≤ n →
      tThr1 p₁ lam₁ p lam p₂ lam₂ n < tThr p₁ lam₁ p lam p₂ lam₂ n ∧
      tThr p₁ lam₁ p lam p₂ lam₂ n < tThr2 p₁ lam₁ p lam p₂ lam₂ n) :
    ∃ (x z : ℕ → ℝ) (F H₁ H₂ V : ℕ → ℝ → ℝ),
      let L₁ : ℕ → ℝ → ℝ := fun n t =>
        PriceSwitch.Markdown.G p lam p₁ lam₁ n t + lam * (V (n - 1) t - PriceSwitch.Markdown.switchRevenue p lam p₁ lam₁ (n - 1) t 0)
      let L₂ : ℕ → ℝ → ℝ := fun n t =>
        PriceSwitch.Markdown.G p lam p₂ lam₂ n t + lam * (V (n - 1) t - PriceSwitch.Markdown.switchRevenue p lam p₂ lam₂ (n - 1) t 0)
      StrictMonoOn x (Set.Ici 1) ∧ StrictMonoOn z (Set.Ici 1) ∧
      (∀ n, 1 ≤ n →
        x n < tThr1 p₁ lam₁ p lam p₂ lam₂ n ∧
        tThr1 p₁ lam₁ p lam p₂ lam₂ n < tThr p₁ lam₁ p lam p₂ lam₂ n ∧
        tThr p₁ lam₁ p lam p₂ lam₂ n < tThr2 p₁ lam₁ p lam p₂ lam₂ n ∧
        tThr2 p₁ lam₁ p lam p₂ lam₂ n < z n) ∧
      (∀ t, V 0 t = 0) ∧
      (∀ n, 1 ≤ n → ∀ t, V n t =
        if x n ≤ t ∧ t ≤ z n then switchNowMax p₁ lam₁ p lam p₂ lam₂ n t + F n t
        else switchNowMax p₁ lam₁ p lam p₂ lam₂ n t) ∧
      (∀ t, F 0 t = 0) ∧
      (∀ n, 1 ≤ n →
        (∀ t, 0 < t → HasDerivAt (H₁ n) (-lam * H₁ n t + L₁ n t) t) ∧
        H₁ n (x n) = 0 ∧
        (∀ t, 0 < t → HasDerivAt (H₂ n) (-lam * H₂ n t + L₂ n t) t) ∧
        H₂ n (tThr p₁ lam₁ p lam p₂ lam₂ n) = H₁ n (tThr p₁ lam₁ p lam p₂ lam₂ n) ∧
        (∃ t, 0 ≤ t ∧ L₁ n t = 0) ∧
        x n = sInf {t : ℝ | 0 ≤ t ∧ L₁ n t = 0} ∧
        (∃ t, tThr p₁ lam₁ p lam p₂ lam₂ n ≤ t ∧ H₂ n t ≤ 0) ∧
        z n = sInf {t : ℝ | tThr p₁ lam₁ p lam p₂ lam₂ n ≤ t ∧ H₂ n t ≤ 0} ∧
        (∀ t, F n t =
          if x n ≤ t ∧ t ≤ tThr p₁ lam₁ p lam p₂ lam₂ n then H₁ n t
          else if tThr p₁ lam₁ p lam p₂ lam₂ n ≤ t ∧ t ≤ z n then H₂ n t
          else 0)) ∧
      (∀ n t, 0 ≤ t → optRevenue3 P T p₁ lam₁ p lam p₂ lam₂ n t = V n t) := by sorry

end PriceSwitch.UpOrDown
