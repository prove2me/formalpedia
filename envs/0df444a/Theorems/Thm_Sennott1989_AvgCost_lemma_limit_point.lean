-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_lemma_limit_point
-- name    : Sennott1989.AvgCost.lemma_limit_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:32.14457+00:00
-- url     : https://prove2.me/theorems/a99990d9-e670-4c40-bf68-8699d98c2544
-- title:
--   Lemma (p. 628) — discount optimal stationary policies along α_n → 1 have a subsequence with a stationary limit point
-- statement:
--   Consider a Markov decision chain on the states $0,1,2,\dots$ with finite action sets. Let $(\alpha_n)$ be a sequence of discount factors in $(0,1)$ converging to $1$, and for each $n$ let $f_{\alpha_n}$ be a stationary policy determined by the right side of the discount optimality equation
--   $$V_{\alpha_n}(i)=\min_{a\in A_i}\Big\{C(i,a)+\alpha_n\sum_jP_{ij}(a)V_{\alpha_n}(j)\Big\},$$
--   i.e. $f_{\alpha_n}(i)$ attains the minimum at every $i$. Then there exist a subsequence $(\beta_n)$ of $(\alpha_n)$ and a stationary policy $f$ that is a limit point of $(f_{\beta_n})$: for every state $i$ there is an integer $N(i)$ with
--   $$f_{\beta_n}(i)=f(i)\qquad\text{for all }n\ge N(i).$$
--
--   The policy $f$ is the candidate for average cost optimality in the paper's Theorem.
--
--   **Formalization Note** The conclusion is `IsLimitPoint` of the published Sennott (1999) development: a strictly increasing index map $r$ with $f_{\alpha_{r(k)}}(i)=f(i)$ for all large $k$, for each $i$.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, §2, Lemma (unnumbered), p. 628

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

/-- Sennott (1989), §2, Lemma (unnumbered), p. 628. Let `α_n` be any sequence of discount factors
in `(0, 1)` converging to `1`, and let `f_{α_n}` be the associated discount optimal stationary
policies, i.e. `f_{α_n}` realizes the minimum in the discount optimality equation (2) at
`α = α_n`. Then there exist a subsequence `(β_n)` of `(α_n)` and a stationary policy `f` that is a
limit point of `(f_{β_n})`: for every state `i` there is an integer `N(i)` with
`f_{β_n}(i) = f(i)` for all `n ≥ N(i)`.

**Formalization Note** "There exist a subsequence and a limit point `f` of `(f_{β_n})`" is
`IsLimitPoint M fs f`: there is a strictly increasing `r : ℕ → ℕ` with `fs (r k) i = f i` for all
sufficiently large `k`, for each `i`. -/
theorem lemma_limit_point {Act : Type} (M : MDC ℕ Act) (αs : ℕ → ℝ≥0)
    (hα0 : ∀ n, 0 < αs n) (hα1 : ∀ n, αs n < 1) (hlim : Tendsto αs atTop (𝓝 1))
    (fs : ℕ → StationaryPolicy M)
    (hfs : ∀ n, Realizes M (fs n) (αs n) (valueFn M (αs n))) :
    ∃ f : StationaryPolicy M, IsLimitPoint M fs f := by sorry

end Sennott1989.AvgCost
