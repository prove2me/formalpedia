-- Prove2me | Theorems.Thm_SennottDP_Discounted_optimal_policy_characterization
-- name    : SennottDP.Discounted.optimal_policy_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T07:21:43.443145+00:00
-- url     : https://prove2.me/theorems/b5116933-8e50-4ce3-8417-c8d6cd3a08b6
-- title:
--   Proposition 4.4.1 — characterization of discount optimal policies by the sets $B_i(\alpha)$
-- statement:
--   Let $\Delta$ be a Markov decision chain and $\alpha \in (0,1)$, and let $B_i(\alpha)$ be the set of actions attaining the minimum in the discount optimality equation (4.9) at state $i$. For a policy $\theta$ for the infinite horizon consider the conditions
--
--   1. given initial state $i$, the distribution $\theta(a \mid i)$ is concentrated on $B_i(\alpha)$;
--   2. for $n \ge 1$, if $h_n$ is a history under $\theta$ with state $i_n$, then the distribution $\theta(a \mid h_n)$ is concentrated on $B_{i_n}(\alpha)$.
--
--   If $\theta$ satisfies (i)–(ii), then $\theta$ is optimal for the infinite horizon expected $\alpha$-discounted cost criterion. Conversely, if $V_\alpha(i) < \infty$ for every $i \in S$ and $\theta$ is optimal, then $\theta$ satisfies (i)–(ii).
--
--   The conditions say that whenever the process is in a state, an optimal policy may only randomize among actions attaining the minimum in (4.9); states never reached from a given initial state are unconstrained.
--
--   **Formalization Note** A "history under $\theta$" is a history of positive probability under $\theta$ from its initial state. The book states the equivalence without a finiteness hypothesis; its necessity argument (equality throughout (4.10)) requires $V_\alpha < \infty$, and without it necessity fails: from an initial state of infinite value, a policy may act suboptimally at a finite-value state it reaches and still be optimal. The necessity direction is therefore stated for finite $V_\alpha$; sufficiency is stated in full generality.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 67–69, Proposition 4.4.1

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.Discounted

/-- Sennott (1999), Proposition 4.4.1, pp. 67–69: a policy `θ` for the infinite horizon is
optimal for the expected `α`-discounted cost criterion if and only if (i) for each initial state
`i` the distribution `θ(a | i)` is concentrated on `B_i(α)`, and (ii) for `n ≥ 1`, if `h_n` is a
history under `θ` with state `i_n`, then `θ(a | h_n)` is concentrated on `B_{i_n}(α)`.
Sufficiency is stated as in the book. Necessity is stated under the additional hypothesis that
`V_α` is finite: the book's necessity argument ("both inequalities in (4.10) must be
equalities") needs `V_α(i) < ∞`, and without it the necessity claim fails (a policy may act
suboptimally after reaching a finite-value state from an initial state with `V_α = ∞`). -/
theorem optimal_policy_characterization {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (θ : Policy M) :
    (ConcentratedOnOptActions M α θ → IsDiscountOptimal M θ α) ∧
      ((∀ i : S, valueFn M α i ≠ ⊤) →
        IsDiscountOptimal M θ α → ConcentratedOnOptActions M α θ) := by sorry

end SennottDP.Discounted
