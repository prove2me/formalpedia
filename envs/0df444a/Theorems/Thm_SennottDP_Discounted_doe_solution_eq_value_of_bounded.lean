-- Prove2me | Theorems.Thm_SennottDP_Discounted_doe_solution_eq_value_of_bounded
-- name    : SennottDP.Discounted.doe_solution_eq_value_of_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T07:15:57.753456+00:00
-- url     : https://prove2.me/theorems/b6483d01-7204-44ff-a658-717473d25510
-- title:
--   Corollary 4.2.4 — finite solutions within a constant of $V_\alpha$, and bounded solutions, equal $V_\alpha$
-- statement:
--   Let $\Delta$ be a Markov decision chain and $\alpha \in (0,1)$.
--
--   1. If $W$ is a finite nonnegative solution of the discount optimality equation (4.9) that satisfies $W \le V_\alpha + B$ for some finite constant $B$, then $W = V_\alpha$.
--   2. If $W$ is a nonnegative bounded solution of (4.9), then $W = V_\alpha$.
--
--   These are the two uniqueness criteria for (4.9) used most often in applications.
--
--   **Formalization Note** The constant $B$ ranges over $[0,\infty)$; this loses nothing, since $W \le V_\alpha + B$ with $B < 0$ implies $W \le V_\alpha + 0$. "Finite" means $W(i) < \infty$ for every $i$; "bounded" means $W \le B$ for a finite constant $B$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 66, Corollary 4.2.4

import Mathlib
import Definitions.Def_SennottDP_Discounted_Optimality

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.Discounted

/-- Sennott (1999), Corollary 4.2.4, p. 66: (i) if `W` is a finite nonnegative solution of the
discount optimality equation (4.9) with `W ≤ V_α + B` for some finite constant `B`, then
`W = V_α`; (ii) if `W` is a nonnegative bounded solution of (4.9), then `W = V_α`.
A constant `B < 0` gives `W ≤ V_α ≤ V_α + 0`, so `B` ranges over `[0, ∞)` without loss. -/
theorem doe_solution_eq_value_of_bounded {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ W : S → ℝ≥0∞, (∀ i, W i ≠ ⊤) → (∀ i, W i = bellman M α W i) →
        (∃ B : ℝ≥0, ∀ i, W i ≤ valueFn M α i + B) → W = valueFn M α) ∧
      (∀ W : S → ℝ≥0∞, (∀ i, W i = bellman M α W i) →
        (∃ B : ℝ≥0, ∀ i, W i ≤ B) → W = valueFn M α) := by sorry

end SennottDP.Discounted
