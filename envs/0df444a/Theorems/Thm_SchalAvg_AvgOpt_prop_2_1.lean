-- Prove2me | Theorems.Thm_SchalAvg_AvgOpt_prop_2_1
-- name    : SchalAvg.AvgOpt.prop_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:05.831994+00:00
-- url     : https://prove2.me/theorems/280521c8-32eb-4c61-90f8-a0efaca5ee28
-- title:
--   Proposition 2.1 — under (W) or (S) a β-discount optimal stationary policy exists and satisfies the discounted optimality equation
-- statement:
--   In Schäl's decision model $(S, A, A(\cdot), q, c)$ (standard Borel spaces, costs in $[0, \infty]$) fix a discount factor $0 < \beta < 1$, and let $v_\beta(x) = \inf_{\delta \in \Delta} J_\beta(\delta, x)$ be the discounted value function.
--
--   1. Under Condition (W) or Condition (S) there is a $\beta$-discount optimal stationary policy $f_\beta \in \mathbb F$, i.e. $J_\beta(f_\beta, x) = v_\beta(x)$ for all $x$.
--   2. Under (W) or (S), every $\beta$-discount optimal stationary policy $f_\beta$ satisfies
--   $$v_\beta(x) = c(x, f_\beta(x)) + \beta \int v_\beta \, dq(x, f_\beta(x)), \qquad x \in S.$$
--   3. Under (W), $v_\beta$ is lower semicontinuous.
--   4. Under (S), $v_\beta$ is measurable.
--
--   This is the discounted existence theorem on which the vanishing-discount analysis rests; the paper cites it from Schäl (1975, §§15, 16).
--
--   **Formalization Note.** The paper's "there exists a discount optimal stationary policy $f_\beta$ which then satisfies" is read as: one exists, and every discount-optimal stationary policy satisfies the equation. Values lie in $[0, \infty]$ and the equation holds there. The General Assumption is not needed. Under (S) the topology on $S$ plays no role.
-- source:
--   Schäl, Average Optimality in Dynamic Programming with General State Space, Math. Oper. Res. 18(1) (1993), p. 166, Proposition 2.1

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt

theorem prop_2_1 {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [TopologicalSpace S]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model S A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    ((CondW M ∨ CondS M) → ∃ f : S → A, IsDiscOptimal M β f) ∧
    ((CondW M ∨ CondS M) → ∀ f : S → A, IsDiscOptimal M β f → ∀ x : S,
      vβ M β x = M.toMDP.cost x (f x) +
        ENNReal.ofReal β * ∫⁻ y, vβ M β y ∂(M.toMDP.q (x, f x))) ∧
    (CondW M → LowerSemicontinuous (vβ M β)) ∧
    (CondS M → Measurable (vβ M β)) := by sorry

end SchalAvg.AvgOpt
