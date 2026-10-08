-- Prove2me | Theorems.Thm_SSPAnalysis_Bellman_lemma3a
-- name    : SSPAnalysis.Bellman.lemma3a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:10:56.649471+00:00
-- url     : https://prove2.me/theorems/217c02c6-1fc7-48e5-a095-571a7c2ce172
-- title:
--   Lemma 3(a) — lower limit of proper-policy costs
-- statement:
--   Under Assumptions 1 and 2, let proper selectors $\mu^k$ converge coordinatewise in their control spaces to a proper selector $\mu$. Then the coordinatewise lower limit of their cost vectors dominates the limiting selector's cost:
--
--   $$\liminf_{k\to\infty}x_i(\mu^k)\ge x_i(\mu)\qquad\text{for every state }i.$$
--
--   This is the lower-semicontinuity part of Lemma 3, used when a policy-improvement sequence has a proper limit.
--
--   **Formalization Note.** Control convergence is coordinatewise in each metric carrier. Costs and the liminf are extended real values. State $1$ is index `0`, and stochastic rows are part of the model.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), p. 586, Lemma 3(a); proof pp. 591–592

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

namespace SSPAnalysis.Bellman

open Filter Topology

/-- Lemma 3(a) (p. 586): lower semicontinuity of proper-policy costs
along a sequence of proper policies converging to a proper policy. -/
theorem lemma3a {n : ℕ} [NeZero n] {U : Fin n → Type*}
    [∀ i, MetricSpace (U i)] (m : Model n U)
    (h1 : m.Assumption1) (h2 : m.Assumption2)
    (μs : ℕ → Selector U) (μ : Selector U)
    (hμs : ∀ k, m.IsProper (μs k))
    (hconv : ∀ i, Tendsto (fun k => μs k i) atTop (𝓝 (μ i)))
    (hμ : m.IsProper μ) :
    ∀ i, m.cost (stationary μ) i ≤
      liminf (fun k => m.cost (stationary (μs k)) i) atTop := by sorry

end SSPAnalysis.Bellman
