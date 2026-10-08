-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_theorem_i
-- name    : Sennott1989.AvgCost.theorem_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:43.007886+00:00
-- url     : https://prove2.me/theorems/1897c65a-791f-456a-ba14-290ffc60c56a
-- title:
--   Theorem (i), p. 628 — under Assumptions 1–3 a limit point f of discount optimal policies is average cost optimal, with g = lim (1 − α)V_α(i) and (5)
-- statement:
--   Consider a Markov decision chain on the states $0,1,2,\dots$ with finite action sets and nonnegative costs, satisfying Assumption 1, Assumption 2 with constant $N\ge0$, and Assumption 3 with bounds $M_i\ge0$. Let $(\alpha_n)\subset(0,1)$ converge to $1$, let $f_{\alpha_n}$ be stationary policies attaining the minimum in the discount optimality equation at $\alpha_n$, and let $f$ be any stationary limit point of a subsequence of $(f_{\alpha_n})$, as given by the Lemma. Then there exist a constant $g$ and a function $h$ such that:
--
--   1. $g=\lim_{\alpha\uparrow1}(1-\alpha)V_\alpha(i)$ for every state $i$;
--   2. $-N\le h(i)\le M_i$ for every $i$;
--   3. for every $i\ge0$,
--   $$g+h(i)\ \ge\ C(i,f)+\sum_jP_{ij}(f)h(j)\ \ge\ \min_{a}\Big\{C(i,a)+\sum_jP_{ij}(a)h(j)\Big\};\tag{5}$$
--   4. $f$ is average cost optimal with average cost $g$: $g=g_f(i)\le g_\theta(i)$ for every policy $\theta$ and every $i$;
--   5. every stationary policy that realizes the minimum in (5) is average cost optimal with average cost $g$.
--
--   This is the paper's main existence result for average cost optimal stationary policies with unbounded costs.
--
--   **Formalization Note** The limit in 1 is the full one-sided limit as $\alpha\to1$, $\alpha<1$, in $[0,\infty]$. Sums against $h$ are extended-real.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, §2, Theorem (i), (5), p. 628; proof in the Appendix, pp. 632–633

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

/-- Sennott (1989), §2, Theorem (unnumbered), part (i), p. 628. Assume Assumptions 1, 2 (with
constant `N`) and 3 (with bounds `M_i`). Let `f` be any stationary policy given by the Lemma: a
limit point of a subsequence of the discount optimal stationary policies `f_{α_n}` along a
sequence of discount factors `α_n ∈ (0, 1)` converging to `1`. Then there exist a constant
`g = lim_{α↑1} (1 − α) V_α(i)` (for every `i`) and a function `h` with `−N ≤ h(i) ≤ M_i` such that
`g + h(i) ≥ C(i, f) + ∑_j P_{ij}(f) h(j) ≥ min_a { C(i, a) + ∑_j P_{ij}(a) h(j) }`, `i ≥ 0` (5).
The stationary policy `f` is average cost optimal with average cost `g`, and any stationary policy
that realizes the minimum in (5) is average cost optimal (with average cost `g`).

**Formalization Note** The limit `lim_{α↑1}` is the full one-sided limit as `α → 1`, `α < 1`
(`IsAbelLimit`), in `[0, ∞]`. The sums are extended-real (`SennottDP.SEN.wsum`). "Average cost
optimal with average cost `g`" is `IsACOptimal`: `g = g_f(i) ≤ g_θ(i)` for every policy `θ` and
every `i`. -/
theorem theorem_i {Act : Type} (M : MDC ℕ Act) (N : ℝ) (Mb : ℕ → ℝ)
    (h1 : Assumption1 M) (h2 : Assumption2 M N) (h3 : Assumption3 M Mb)
    (αs : ℕ → ℝ≥0) (hα0 : ∀ n, 0 < αs n) (hα1 : ∀ n, αs n < 1) (hlim : Tendsto αs atTop (𝓝 1))
    (fs : ℕ → StationaryPolicy M)
    (hfs : ∀ n, Realizes M (fs n) (αs n) (valueFn M (αs n)))
    (f : StationaryPolicy M) (hf : IsLimitPoint M fs f) :
    ∃ (g : ℝ) (h : ℕ → ℝ), IsAbelLimit M g ∧ (∀ i, -N ≤ h i ∧ h i ≤ Mb i) ∧ ACOI M g h f ∧
      IsACOptimal M f g ∧ ∀ e : StationaryPolicy M, RealizesACOI M h e → IsACOptimal M e g := by sorry

end Sennott1989.AvgCost
