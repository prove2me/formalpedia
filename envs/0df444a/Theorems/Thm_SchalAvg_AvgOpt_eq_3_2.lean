-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_eq_3_2
-- name    : SchalAvg.AvgOpt.eq_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:34.222551+00:00
-- url     : https://prove2.me/theorems/5d0ef280-8d43-4595-95ef-974382405cc3
-- title:
--   (3.2), corrected — inf_{k≥n} w̲_n(k, x) increases to w̲(x)
-- statement:
--   Let the state space $S$ of Schäl's decision model carry a metric $\rho$ defining its topology, let $\beta(k)$ be a sequence of discount factors, and write $w(k, x) = w_{\beta(k)}(x)$,
--   $$\underline w(x) = \liminf_{k \to \infty,\ y \to x} w(k, y), \qquad \underline w_n(k, x) = \inf_{\rho(x, y) \le 1/n} w(k, y) \quad (n \ge 1).$$
--   Then for every $x \in S$, as $n \to \infty$,
--   $$\inf_{k \ge n} \underline w_n(k, x) \ \uparrow\ \underline w(x),$$
--   that is, the left-hand side is nondecreasing in $n \ge 1$ and converges to $\underline w(x)$.
--
--   This identity represents the generalized lower limit $\underline w$ through countably many ball infima, which is how its measurability and the measurable approximating sequences of Lemma 3.4 are obtained.
--
--   **Formalization Note.** The paper prints (3.2) as $\inf_{k \ge n} \underline w_k(k, x) \uparrow \underline w(x)$, with subscript $k$. That diagonal version is false in general (take $w(k, \cdot) = 0$ at one point at distance $2/k$ from $x$ and $1$ elsewhere: $\underline w(x) = 0$ while every $\underline w_k(k, x) = 1$). The proof of Lemma 3.4 (p. 167) uses the subscript-$n$ version, which is stated here. Monotonicity is asserted for $n \ge 1$ (the radius $1/n$ is undefined at $n = 0$; Lean's $1/0 = 0$ would make the $n = 0$ ball $\{x\}$). The statement needs no assumption on the model; it holds for every sequence $\beta(k)$, a harmless generalization of the paper's fixed sequence.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), p. 166, (3.2) (read with subscript n as in the proof of Lemma 3.4, p. 167)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem eq_3_2 {S A : Type*} [MetricSpace S] [MeasurableSpace S] [MeasurableSpace A]
    (M : Model S A) (β : ℕ → ℝ) (x : S) :
    MonotoneOn (fun n : ℕ => ⨅ k ≥ n, wBall M β n k x) (Set.Ici 1) ∧
    Tendsto (fun n : ℕ => ⨅ k ≥ n, wBall M β n k x) atTop (𝓝 (wLow M β x)) := by sorry

end SchalAvg.AvgOpt
