-- Prove2me | Theorems.Thm_SRPTManyServer_Collapse_capacity_constraint_5
-- name    : SRPTManyServer.Collapse.capacity_constraint_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:11.659122+00:00
-- url     : https://prove2.me/theorems/e7ccb5cf-03ff-41c3-92f2-e7d5e2d5557a
-- title:
--   Eq. (5), p. 16 — the rate of completed work never exceeds the capacity $s$ (pathwise form)
-- statement:
--   Consider an admissible sample path and an SRPT schedule with $s$ servers. For every $t \ge 0$, the total service requirement of the customers who have finished service by time $t$ is at most $s\,t$:
--   $$\sum_{n:\ \text{served by } t} S_n \;\le\; s\,t.$$
--
--   Dividing by $t$ and letting $t \to \infty$ gives the paper's capacity constraint (5): the long-run rate at which work is completed, $\lambda\int_0^\infty x g(x)\gamma^\lambda(x)\,dx$, where $\gamma^\lambda(x)$ is the steady-state probability that a customer with service time $x$ is served, is at most $s^\lambda$. In the paper's words, the stationary number of customers in service is less than the service capacity.
--
--   **Formalization Note** The paper states (5) in steady state, in terms of $\gamma^\lambda$. This item is the pathwise inequality from which (5) follows by dividing by $t$. It is stated pathwise because $\gamma^\lambda$ is not a primitive of the model.
-- source:
--   Dong & Ibrahim, On the SRPT scheduling discipline in many-server queues with impatient customers, arXiv:2102.05789v1, p. 16, eq. (5)

import Mathlib
import Definitions.Def_SRPTManyServer_Collapse_Model

namespace SRPTManyServer.Collapse

/-- **Capacity constraint (5)** (p. 16), pathwise form. On an admissible sample path, under an SRPT
schedule with `s` servers, the total service requirement of the customers who have finished service
by time `t ≥ 0` is at most `s · t`: the long-run rate at which work is completed,
`λ ∫ x g(x) γ^λ(x) dx` in the paper's notation, never exceeds the service capacity `s`. -/
theorem capacity_constraint_5 (s : ℕ) (x : Stream) (hx : x.Admissible) (δ : ℕ → ℝ → ℝ)
    (hδ : IsSRPTSchedule s x δ) (t : ℝ) (ht : 0 ≤ t) :
    completedWork x δ t ≤ (s : ℝ) * t := by sorry

end SRPTManyServer.Collapse
