-- Prove2me | Theorems.Thm_SchrageSRPT_Opt_srpt_optimal
-- name    : SchrageSRPT.Opt.srpt_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:43.764106+00:00
-- url     : https://prove2.me/theorems/bcee4e75-8807-40f9-b3d1-8c3eb0f6f0ce
-- title:
--   PROOF, p. 689 (claim quoted on p. 687) — under SRPT the number in system at every time is ≤ that under any other schedule of the same arrival stream
-- statement:
--   Let $\{A(n), P(n)\}_{n \ge 0}$ be an arrival stream in which only finitely many jobs arrive by any given time: $\{n : A(n) \le t\}$ is finite for every $t \in \mathbb R$. Let $\delta_s$ be a schedule of this stream that follows the Shortest Remaining Processing Time discipline (at every time at which some job is in system, the processor serves a job in system with the smallest remaining processing time), and let $\delta$ be any schedule of the same stream. Then at every time $t$,
--   $$N_s(t) \le N(t),$$
--   where $N_s(t)$ and $N(t)$ are the numbers of jobs in system at time $t$ under $\delta_s$ and $\delta$.
--
--   In the letter's words: "the number in system at any point in time under the SRPT discipline is always less than or equal to the number in system at the same point in time for the same arrival stream under a non-SRPT discipline". No assumption is made on the distribution of interarrival or processing times: the comparison is pathwise, for every arrival stream. By Little's law it implies that SRPT minimizes the mean number in system and the mean response time in any single-server queue.
--
--   **Formalization Note.** The competitor $\delta$ ranges over every schedule of the stream (measurable, $\{0,1\}$-valued, no service before arrival, at most one job at a time); it may idle, preempt arbitrarily, or serve jobs that have completed. Including SRPT schedules among the competitors also covers the comparison between two tie-breaking choices. SRPT is the verbal rule of p. 687, which forces the processor to work whenever a job is in system; the displayed condition of p. 688 alone is satisfied by the schedule that never processes anything, for which the claim is false. The comparison holds at every time $t$, not almost every $t$. A job is in system on $[A(n), C(n))$. Local finiteness of arrivals is added so that the number in system is a genuine count. Jobs are indexed from $0$.
-- source:
--   Schrage, A proof of the optimality of the shortest remaining processing time discipline, Oper. Res. 16 (1968), p. 689, PROOF (last sentence); statement quoted from Miller–Schrage (1966) on p. 687

import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem srpt_optimal (A P : ℕ → ℝ) (hfin : ∀ t : ℝ, {n | A n ≤ t}.Finite)
    (δs δ : ℕ → ℝ → ℝ) (hs : IsSRPT A P δs) (hδ : IsSchedule A δ) :
    ∀ t : ℝ, numInSystem A P δs t ≤ numInSystem A P δ t := by sorry
end SchrageSRPT.Opt
