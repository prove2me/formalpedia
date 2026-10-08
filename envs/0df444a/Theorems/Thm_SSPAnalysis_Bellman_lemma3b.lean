-- Prove2me | Theorems.Thm_SSPAnalysis_Bellman_lemma3b
-- name    : SSPAnalysis.Bellman.lemma3b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:11:15.517981+00:00
-- url     : https://prove2.me/theorems/e0a0b92e-5807-4dbf-a113-9437d14b1966
-- title:
--   Lemma 3(b) — costs diverge near an improper limit policy
-- statement:
--   Under Assumptions 1 and 2, let each selector $\mu^k$ be proper and suppose $\mu^k$ converges coordinatewise to an improper selector $\mu$. Then at least one initial state has costs unbounded above along the sequence:
--
--   $$\exists i\;\forall M\in\mathbb R\;\exists k:\ x_i(\mu^k)>M.$$
--
--   This prevents a bounded decreasing sequence of proper-policy costs from approaching an improper selector in the main argument.
--
--   **Formalization Note.** Costs are extended real, while thresholds are real. Convergence is coordinatewise in the compact metric control spaces. The statement includes the full preamble of Lemma 3 rather than treating part (b) in isolation. State $1$ is index `0`.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), p. 586, Lemma 3(b); proof pp. 592–595

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

namespace SSPAnalysis.Bellman

open Filter Topology

/-- Lemma 3(b) (p. 586): when proper policies approach an improper
policy, one initial state's costs are unbounded above. -/
theorem lemma3b {n : ℕ} [NeZero n] {U : Fin n → Type*}
    [∀ i, MetricSpace (U i)] (m : Model n U)
    (h1 : m.Assumption1) (h2 : m.Assumption2)
    (μs : ℕ → Selector U) (μ : Selector U)
    (hμs : ∀ k, m.IsProper (μs k))
    (hconv : ∀ i, Tendsto (fun k => μs k i) atTop (𝓝 (μ i)))
    (hμ : ¬ m.IsProper μ) :
    ∃ i, ∀ M : ℝ, ∃ k, (M : EReal) < m.cost (stationary (μs k)) i := by sorry

end SSPAnalysis.Bellman
