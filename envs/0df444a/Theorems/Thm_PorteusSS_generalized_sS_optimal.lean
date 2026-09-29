-- Prove2me | Theorems.Thm_PorteusSS_generalized_sS_optimal
-- name    : PorteusSS.generalized_sS_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:59:06.12778+00:00
-- url     : https://prove2.me/theorems/3872a132-3fb3-4702-b8f1-f23750ca8b79
-- title:
--   Theorem 3 — a generalized $(s,S)$ policy is optimal in every period of the finite-horizon problem
-- statement:
--   Consider the periodic-review inventory model with immediate delivery and full backlogging: $c$ is a concave increasing ordering cost with $c(0) = 0$ whose supporting-line pairs $C_2(z)$ converge to $(c_0, K_0)$ as $z \downarrow 0$ and to $(c_\infty, K_\infty)$ as $z \to \infty$; the discount factor satisfies $0 \le \alpha \le 1$; demands are i.i.d. with a one-sided Pólya density $\varphi$; the holding-and-shortage cost $m$ is PF-integrable, bounded below and piecewise continuous; $f_0$ is the terminal cost. Let $f_n$, $h_n$ and $Y_n$ be defined by the recursion
--   $$ h_n = m * \varphi + \alpha\, f_{n-1} * \varphi, \qquad f_n(x) = \inf_{y \ge x}\{c(y - x) + h_n(y)\}, $$
--   with $Y_n(x)$ the set of minimizing post-order levels. If A1–A5 hold, then for every period $n \ge 1$:
--
--   1. the convolution $f_{n-1} * \varphi$ exists (the integral is finite) at every point, and
--   2. a generalized $(s,S)$ policy is optimal in period $n$: there are $s, S \in \mathbb R$ and a generalized $(s,S)$ policy $y$ with
--   $$ y(x) \in Y_n(x) \qquad \text{for every } x \in \mathbb R . $$
--
--   This extends Scarf's optimality of $(s,S)$ policies from setup-plus-linear ordering costs to arbitrary concave increasing ordering costs, at the price of a larger class of policies and of a demand density restricted to one-sided Pólya densities.
--
--   **Formalization Note.** The model is stationary, so "optimal in any finite horizon problem" (every horizon $N$ and every period $n \le N$) is stated as "every $n \ge 1$". Conclusion (1) guarantees $h_n$ is a genuine integral, and conclusion (2) forces $Y_n(x) \ne \emptyset$, so the infimum defining $f_n$ is attained; neither is assumed. The paper uses without stating it that $m$ is piecewise continuous (proof of Lemma 3); it is the hypothesis `hm_pc`. Measurability of $m$ and $f_0$ (§X) follows from their piecewise continuity.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 419, Theorem 3

import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost
import Definitions.Def_PorteusSS_Model

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Theorem 3 (p. 419). In the model of §§II–III, with `m` piecewise continuous, if A1–A5 hold
then in every period `n ≥ 1` of the finite-horizon problem (a) the convolution `f_{n-1} * φ`
defining `h_n` exists at every point, and (b) a generalized `(s, S)` policy is optimal: there are
`s, S` and a generalized `(s, S)` policy `pol` with `pol x ∈ Y_n(x)` for every `x`. -/
theorem generalized_sS_optimal (c m φ f0 : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ)
    (hmodel : IsModel c m φ α c0 K0 cInf KInf) (hm_pc : PiecewiseContinuousOn m univ)
    (hA1 : AssumptionA1 m α c0 cInf) (hA2 : AssumptionA2 m α c0 cInf)
    (hA3 : AssumptionA3 c m α) (hA4 : AssumptionA4 m α cInf)
    (hA5 : AssumptionA5 c f0 cInf) :
    ∀ n : ℕ, 1 ≤ n →
      (∀ y : ℝ, Integrable (fun ξ => valueFn c m φ f0 α (n - 1) (y - ξ) * φ ξ)) ∧
      ∃ s S : ℝ, ∃ pol : ℝ → ℝ, IsGenSS pol s S ∧ ∀ x : ℝ, pol x ∈ Yset c m φ f0 α n x := by sorry

end PorteusSS
