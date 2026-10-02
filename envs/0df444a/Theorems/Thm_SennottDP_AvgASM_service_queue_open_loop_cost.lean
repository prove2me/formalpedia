-- Prove2me | Theorems.Thm_SennottDP_AvgASM_service_queue_open_loop_cost
-- name    : SennottDP.AvgASM.service_queue_open_loop_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T09:56:04.181207+00:00
-- url     : https://prove2.me/theorems/b6da2be9-ef67-44ed-9e45-d7dde232e4f2
-- title:
--   Proposition 8.5.1 — average cost of serving at a constant rate a > p
-- statement:
--   In the single-server queue with service rate control, Bernoulli($p$) arrivals, holding cost $H(i)=Hi$ and service cost $C(a)$, let the allowable service rate $a$ satisfy $p<a$, and let $d(a)$ be the policy that always serves at rate $a$. Then for every initial state $i$ the average cost of $d(a)$ is
--   $$J_{d(a)}=\frac{Hp(1-p)}{a-p}+\frac{pC(a)}{a}. \tag{8.12}$$
--
--   The quantity $\min_{a>p}J_{d(a)}$ is the benchmark ("open loop control") against which the average cost optimal policies computed in Section 8.5 are compared.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 182, Proposition 8.5.1, (8.12)

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Criteria
import Definitions.Def_SennottDP_AvgASM_ServiceQueue

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Proposition 8.5.1** (Sennott 1999, p. 182). In the single-server queue with service rate
control and Bernoulli(`p`) arrivals, holding cost `H(i) = H i` and service cost `C(a)`, let the
allowable rate `a` satisfy `p < a`, and let `d(a)` be the policy that always serves at rate `a`.
Then, from every initial state `i`,
`J_{d(a)} = H p (1 − p)/(a − p) + p C(a)/a` (8.12). -/
theorem service_queue_open_loop_cost (Q : ServiceQueueData) (a : ℝ) (ha : a ∈ Q.rates)
    (hpa : Q.p < a) (i : ℕ) :
    avgCost (Q.serveAt a ha).toPolicy i =
      ENNReal.ofReal ((Q.H : ℝ) * Q.p * (1 - Q.p) / (a - Q.p) + Q.p * (Q.serviceCost a : ℝ) / a) := by sorry

end SennottDP.AvgASM
