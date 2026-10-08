-- Prove2me | Theorems.Thm_SSPAnalysis_Bellman_equation15
-- name    : SSPAnalysis.Bellman.equation15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:11:12.585709+00:00
-- url     : https://prove2.me/theorems/3866555f-31ca-4340-9a0d-6caf50650b0b
-- title:
--   Equation (15) — proper policy improvement weakly lowers costs
-- statement:
--   Under Assumptions 1 and 2, start with a proper selector $\mu$ and choose $\mu'$ whose Bellman value at $x(\mu)$ attains the minimum of $T$. Then $\mu'$ is proper and has no larger cost from any state:
--
--   $$T_{\mu'}(x(\mu))=T(x(\mu))\quad\Longrightarrow\quad \mu'\text{ proper and }x(\mu')\le x(\mu).$$
--
--   This is the policy-improvement step used to construct the descending sequence in Proposition 2.
--
--   **Formalization Note.** The initial selector's finite real cost vector is named explicitly and identified coordinatewise with its extended-real policy cost. Its existence follows from properness; finiteness is not assumed for the optimal cost. State $1$ is index `0`.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), p. 587, proof of Proposition 2, equation (15) and preceding sentences

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

namespace SSPAnalysis.Bellman

open Filter Topology

/-- Equation (15) (p. 587): a greedy policy improvement from a proper
policy remains proper and weakly lowers its cost vector. -/
theorem equation15 {n : ℕ} [NeZero n] {U : Fin n → Type*}
    [∀ i, MetricSpace (U i)] (m : Model n U)
    (h1 : m.Assumption1) (h2 : m.Assumption2)
    (μ μ' : Selector U) (hμ : m.IsProper μ)
    (xr : Fin n → ℝ)
    (hxr : ∀ i, (xr i : EReal) = m.cost (stationary μ) i)
    (hgreedy : m.Tmu μ' xr = m.T xr) :
    m.IsProper μ' ∧
      ∀ i, m.cost (stationary μ') i ≤ m.cost (stationary μ) i := by sorry

end SSPAnalysis.Bellman
