-- Prove2me | Theorems.Thm_SSPAnalysis_Bellman_equation24
-- name    : SSPAnalysis.Bellman.equation24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:11:11.910341+00:00
-- url     : https://prove2.me/theorems/fc385763-ea58-43c7-95e7-e567a155008a
-- title:
--   Appendix equation (24) — infinite cost outside states reaching the destination
-- statement:
--   Under Assumption 1, let $\mu$ be improper. If an initial state $i$ cannot reach state $1$ by a positive-probability path under $P(\mu)$, then its stationary-policy cost is infinite:
--
--   $$x_i(\mu)=+\infty\qquad\text{whenever state }1\text{ is unreachable from }i.$$
--
--   This is equation (24), the key infinite-cost claim within the proof of Lemma 3(b).
--
--   **Formalization Note.** Reachability requires a positive integer power of the transition matrix with a positive $(i,1)$ entry. State $1$ is index `0`; the theorem names only other states because the destination itself is in the paper's reachable set by definition. The extended-real cost records infinity directly. Assumption 2 is not imposed.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), p. 592, Appendix, proof of Lemma 3(b), equation (24)

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

namespace SSPAnalysis.Bellman

open Filter Topology

/-- Appendix equation (24) (p. 592): every state outside the set of
states that can reach state 1 has infinite cost under an improper policy. -/
theorem equation24 {n : ℕ} [NeZero n] {U : Fin n → Type*}
    (m : Model n U) (h1 : m.Assumption1)
    (μ : Selector U) (hμ : ¬ m.IsProper μ) :
    ∀ i, i ≠ 0 → ¬ Reaches (m.P μ) i 0 →
      m.cost (stationary μ) i = ⊤ := by sorry

end SSPAnalysis.Bellman
