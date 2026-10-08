-- Prove2me | Theorems.Thm_Reiman84_QueueLength_queue_equations_exists_unique
-- name    : Reiman84.QueueLength.queue_equations_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:48:23.604828+00:00
-- url     : https://prove2.me/theorems/5aa7a270-167f-4928-b0bb-95facfe46cd6
-- title:
--   Section 2, Eqs. (1)–(3) — existence and uniqueness of the queue-length and busy-time processes
-- statement:
--   Consider one network of §2 and fix a sample point $\omega$ at which the partial sums of the interarrival times, $U_k(l)$ for $k\in\mathcal J$, and of the service times, $V_k(l)$ for $1\le k\le K$, tend to infinity as $l\to\infty$. Then there exist processes $Q_1(t),\dots,Q_K(t)$, $B_1(t),\dots,B_K(t)$, $t\ge0$, which simultaneously satisfy
--   $$Q(0)\in\mathbb Z^K_+,\qquad B_k(0)=0,\qquad B_k(t)=\int_0^t1_{\{Q_k(s)>0\}}\,ds,\qquad Q(t)=A(t)+\sum_{k=1}^K\hat S_k(B_k(t)),$$
--   and any two such pairs coincide for all $t\ge0$.
--
--   Theorem 1 is a statement about this process; the result shows that the hypothesis "$(Q^n,B^n)$ solves (1)–(3)" used in the other items is satisfiable and pins the process down.
--
--   **Formalization Note** The paper states the claim without conditions and omits the proof ("straightforward but messy"). The condition $U_k(l)\to\infty$, $V_k(l)\to\infty$ at $\omega$ is implicit in the definition of $A_k(t)$, $S_k(t)$ as maxima (p. 443): without it the maxima need not exist. It holds almost surely. Solutions are required to have Lebesgue measurable paths $s\mapsto Q_k(s)$ so that (2) is meaningful.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), p. 443, Section 2, claim preceding Eqs. (1a)–(3)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Network

namespace Reiman84.QueueLength

open Filter Topology MeasureTheory

/-- Section 2, Eqs. (1)–(3), p. 443: at every sample point where the partial sums of the
interarrival and service times tend to infinity, there exist unique processes
`Q_1, …, Q_K, B_1, …, B_K` (on `t ≥ 0`) satisfying (1a), (1b), (2), (3). -/
theorem queue_equations_exists_unique {K : ℕ} {J : Finset (Fin K)} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (N : Network K J P) (ω : Ω)
    (hU : ∀ k ∈ J, Tendsto (fun l => N.U k l ω) atTop atTop)
    (hV : ∀ k, Tendsto (fun l => N.V k l ω) atTop atTop) :
    (∃ Q B : ℝ → Fin K → ℝ, N.IsQueueSolution ω Q B) ∧
    ∀ Q B Q' B' : ℝ → Fin K → ℝ, N.IsQueueSolution ω Q B → N.IsQueueSolution ω Q' B' →
      ∀ t, 0 ≤ t → Q t = Q' t ∧ B t = B' t := by sorry

end Reiman84.QueueLength
