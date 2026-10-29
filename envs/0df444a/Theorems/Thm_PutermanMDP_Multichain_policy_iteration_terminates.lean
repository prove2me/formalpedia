-- Prove2me | Theorems.Thm_PutermanMDP_Multichain_policy_iteration_terminates
-- name    : PutermanMDP.Multichain.policy_iteration_terminates
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T03:01:19.642983+00:00
-- url     : https://prove2.me/theorems/5737d147-a503-4f27-b036-09eeb491002d
-- title:
--   Theorem 9.2.3 — finite termination of multichain policy iteration
-- statement:
--   Let $S$ and every $A_s$ be finite. Run the multichain policy iteration algorithm of §9.2.1 from an arbitrary admissible rule. At every iteration solve the evaluation equations and use the canonical stationary bias $h_n=h^{(d_n)^\infty}$. The assertion is that there is a finite stopping index $N$ such that
--   $$d_{N+1}=d_N,\qquad(d_N)^\infty\text{ is average optimal},\qquad(g_N,h_N)\text{ satisfies (9.1.5) and (9.1.6)}.$$
--   Average optimality compares the stationary policy's lower average reward with the upper average reward of every history-dependent randomized policy. The conclusion concerns both the returned policy and the evaluated gain/bias pair.
--
--   **Formalization Note** This faithful goal uses phase-two maximization over all actions exactly as printed in (9.2.4) and (9.2.8). It is expected to be disproved: finding F3 supplies a two-state cycle despite canonical evaluation. The separately corrected item restricts phase two to gain-preserving actions. Runs here start at zero and are extended constantly after stopping; no termination assumption appears in the run predicate.
-- source:
--   Puterman, Markov Decision Processes: Discrete Stochastic Dynamic Programming, Wiley, 1994, https://doi.org/10.1002/9780470316887, p. 457 (PDF 473), Theorem 9.2.3; algorithm pp. 452–453 (PDF 468–469)

import Mathlib
import Definitions.Def_PutermanMDP_Multichain_Iteration

open MarkovDecisionProcesses Filter
open scoped Topology

namespace PutermanMDP.Multichain

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty S]

/-- Theorem 9.2.3, p. 457 (PDF 473), for the algorithm as printed in §9.2.1.
Finding F3 records a cycle; the printed goal is preserved, not silently corrected. -/
theorem policy_iteration_terminates (M : StationaryMDP S A)
    (d : ℕ → Rule M) (g h : ℕ → S → ℝ) (hrun : PrintedRun M d g h) :
    ∃ N : ℕ, d (N + 1) = d N ∧ IsAverageOptimal (policy M (d N)) ∧
      OptimalityEquations M (g N) (h N) := by sorry

end PutermanMDP.Multichain
