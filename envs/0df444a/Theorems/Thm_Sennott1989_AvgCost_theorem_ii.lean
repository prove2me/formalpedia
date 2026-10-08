-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_theorem_ii
-- name    : Sennott1989.AvgCost.theorem_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:34.231834+00:00
-- url     : https://prove2.me/theorems/97cd7ae2-890c-4861-a87b-697e842f9e47
-- title:
--   Theorem (ii), p. 628 — under Assumptions 1, 2 and 3* the g and h of part (i) satisfy the average cost optimality equation (6)
-- statement:
--   Under the hypotheses of Theorem (i) with Assumption 3 strengthened to Assumption 3\* (same bounds $M_i$), and for every stationary policy $f$ given by the Lemma, the constant $g$ and the function $h$ of part (i) satisfy, in addition to all conclusions of part (i), the average cost optimality equation
--   $$g+h(i)=\min_{a}\Big\{C(i,a)+\sum_jP_{ij}(a)h(j)\Big\},\qquad i\ge0.\tag{6}$$
--   That is, there exist $g$ and $h$ with $g=\lim_{\alpha\uparrow1}(1-\alpha)V_\alpha(i)$ for all $i$, $-N\le h\le M$, (5), $f$ average cost optimal with average cost $g$, every minimizer of (5) average cost optimal, and (6).
--
--   Under the slightly stronger Assumption 3\*, the optimality inequality of part (i) becomes an equation.
--
--   **Formalization Note** One existential carries all the conclusions, so that (6) is asserted for the same $g$ and $h$ as part (i), not for an arbitrary pair.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, §2, Theorem (ii), (6), p. 628

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

/-- Sennott (1989), §2, Theorem (unnumbered), part (ii), p. 628, together with part (i). Assume
Assumptions 1, 2 (with constant `N`) and 3* (with bounds `M_i`), and let `f` be any stationary
policy given by the Lemma (as in `theorem_i`). Then the constant `g` and the function `h` of part
(i) satisfy, besides all the conclusions of part (i), the average cost optimality equation
`g + h(i) = min_a { C(i, a) + ∑_j P_{ij}(a) h(j) }`, `i ≥ 0` (6).

**Formalization Note** "g and h(i) from (i)" is rendered by one existential whose witnesses
satisfy every conclusion of part (i) and (6). -/
theorem theorem_ii {Act : Type} (M : MDC ℕ Act) (N : ℝ) (Mb : ℕ → ℝ)
    (h1 : Assumption1 M) (h2 : Assumption2 M N) (h3 : Assumption3Star M Mb)
    (αs : ℕ → ℝ≥0) (hα0 : ∀ n, 0 < αs n) (hα1 : ∀ n, αs n < 1) (hlim : Tendsto αs atTop (𝓝 1))
    (fs : ℕ → StationaryPolicy M)
    (hfs : ∀ n, Realizes M (fs n) (αs n) (valueFn M (αs n)))
    (f : StationaryPolicy M) (hf : IsLimitPoint M fs f) :
    ∃ (g : ℝ) (h : ℕ → ℝ), IsAbelLimit M g ∧ (∀ i, -N ≤ h i ∧ h i ≤ Mb i) ∧ ACOI M g h f ∧
      IsACOptimal M f g ∧ (∀ e : StationaryPolicy M, RealizesACOI M h e → IsACOptimal M e g) ∧
      ACOE M g h := by sorry

end Sennott1989.AvgCost
