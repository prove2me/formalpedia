-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_lemma_3_3
-- name    : SchalAvg.AvgOpt.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:08.049762+00:00
-- url     : https://prove2.me/theorems/b3cffaaf-0aa7-44e6-bc14-587cd0f394d7
-- title:
--   Lemma 3.3 — under (W) and (B), a measurable 1/n-near minimizer φ_{k,n} of w(k, ·) on the ball of radius 1/n
-- statement:
--   In Schäl's decision model $(S, A, A(\cdot), q, c)$ let $\rho$ be a metric on $S$ defining its topology, and assume the General Assumption, Condition (W) and Condition (B). Let $\beta(k)$ be discount factors in $(0, 1)$, $w(k, x) = w_{\beta(k)}(x)$, and $\underline w_n(k, x) = \inf_{\rho(x, y) \le 1/n} w(k, y)$. Then for every $k$ and every $n \ge 1$ there is a mapping $\varphi = \varphi_{k,n} : S \to S$ such that
--
--   1. $\varphi$ is measurable,
--   2. $\rho(\varphi(x), x) \le 1/n$ for all $x$,
--   3. $$w(k, \varphi(x)) \le \underline w_n(k, x) + \frac1n \quad \text{for all } x.$$
--
--   The selector $\varphi_{k,n}$ turns the ball infimum $\underline w_n(k, \cdot)$ into a value attained, up to $1/n$, at a measurably chosen nearby point; it is the building block of the measurable sequences of Lemma 3.4.
--
--   **Formalization Note.** The General Assumption is the paper's standing assumption; it gives $m_\beta < \infty$, so $w(k, \cdot)$ is the true difference $v_{\beta(k)} - m_{\beta(k)}$. The paper's fixed sequence $\beta(k)$ with (3.1) is replaced by an arbitrary sequence in $(0, 1)$; neither $\beta(k) \to 1$ nor (3.1) is used, so this is a harmless generalization. The metric is a `MetricSpace` instance on $S$; Condition (W) then ties its topology to the Borel σ-algebra and makes it locally compact with countable base.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), p. 166, Lemma 3.3

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem lemma_3_3 {S A : Type*} [MetricSpace S] [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model S A) (hGA : GeneralAssumption M) (hW : CondW M) (hB : CondB M)
    (β : ℕ → ℝ) (hβ : ∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) (k n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : S → S, Measurable φ ∧ ∀ x : S, dist (φ x) x ≤ 1 / (n : ℝ) ∧
      wβ M (β k) (φ x) ≤ wBall M β n k x + (n : ℝ≥0∞)⁻¹ := by sorry

end SchalAvg.AvgOpt
