-- Prove2me | Theorems.Thm_SRPTManyServer_Collapse_proposition_1
-- name    : SRPTManyServer.Collapse.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:04.542147+00:00
-- url     : https://prove2.me/theorems/32858e22-cdf5-4061-8011-35842b8e9a04
-- title:
--   Proposition 1, p. 8 — for the coupled SRPT and loss queues, $\mathrm{Th}_{L,1} \le \mathrm{Th}_O$
-- statement:
--   Fix $s$ servers, a threshold $\tau$ and an admissible sample path of arrival, service and patience times. Run on this path both the SRPT queue $O$ with abandonment, under any SRPT schedule, and the coupled two-class preemptive priority loss system $L$ in which class 1 consists of the customers with $S_n \le \tau$. Both systems start empty and see exactly the same customers. Let $N_{L,1}(t)$ be the number of class 1 customers served in $L$ by time $t$, and $N_O(t)$ the number of customers served in $O$ by time $t$. If the throughputs
--   $$\mathrm{Th}_{L,1} = \lim_{t\to\infty}\frac{N_{L,1}(t)}{t},\qquad \mathrm{Th}_O = \lim_{t\to\infty}\frac{N_O(t)}{t}$$
--   exist, then
--   $$\mathrm{Th}_{L,1} \le \mathrm{Th}_O.$$
--
--   This is the coupling at the heart of the paper. It lets the known throughput of the loss system, which is Erlang-type, bound the throughput of SRPT from below. The paper's proof matches customers so that $N_{L,1}(t) \le N_O(t)$ for every $t \ge 0$, sample path by sample path.
--
--   **Formalization Note** The proposition is stated for one deterministic admissible path and every SRPT schedule of it, which covers every tie-breaking rule. The threshold $\tau$ is arbitrary here; the statement does not use equation (1).
-- source:
--   Dong & Ibrahim, On the SRPT scheduling discipline in many-server queues with impatient customers, arXiv:2102.05789v1, p. 8, Proposition 1 (eq. (3)), with (2) on p. 8

import Mathlib
import Definitions.Def_SRPTManyServer_Collapse_Model

namespace SRPTManyServer.Collapse

open Filter Topology

/-- **Proposition 1** (p. 8). On one admissible sample path, the SRPT system with `s` servers and
schedule `δ` and the coupled two-class preemptive priority loss system with threshold `τ` see the
same customers and start empty. If the class 1 throughput `Th_{L,1} = lim N_{L,1}(t)/t` of the loss
system and the total throughput `Th_O = lim N_O(t)/t` of the SRPT system exist, then
`Th_{L,1} ≤ Th_O`. -/
theorem proposition_1 (s : ℕ) (tau : ℝ) (x : Stream) (hx : x.Admissible) (δ : ℕ → ℝ → ℝ)
    (hδ : IsSRPTSchedule s x δ) (thL1 thO : ℝ)
    (hL : Tendsto (fun t : ℝ => (lossNumCompleted1 s tau x t : ℝ) / t) atTop (𝓝 thL1))
    (hO : Tendsto (fun t : ℝ => (numCompleted x δ t : ℝ) / t) atTop (𝓝 thO)) :
    thL1 ≤ thO := by sorry

end SRPTManyServer.Collapse
