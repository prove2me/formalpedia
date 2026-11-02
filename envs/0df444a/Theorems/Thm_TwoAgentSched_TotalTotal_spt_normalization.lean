-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_spt_normalization
-- name    : TwoAgentSched.TotalTotal.spt_normalization
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T19:12:55.963353+00:00
-- url     : https://prove2.me/theorems/40ebd38f-f9a4-45b5-8454-eec6068b57fd
-- title:
--   Agentwise SPT normalization does not increase either total completion time
-- statement:
--   Let $I$ be a two-agent single-machine instance. Each agent's jobs are indexed in nondecreasing order of their nonnegative integer processing times. A schedule is a sequence containing each job exactly once, and $S_A(\sigma)$ and $S_B(\sigma)$ are the agents' respective sums of job completion times in schedule $\sigma$.
--
--   For every schedule $\sigma$, there exists a schedule $\sigma^*$ in which the jobs of each agent occur in strictly increasing index order and
--
--   $$
--   S_A(\sigma^*)\le S_A(\sigma),\qquad S_B(\sigma^*)\le S_B(\sigma).
--   $$
--
--   The two agents' jobs may be interleaved arbitrarily, and processing times may be zero or equal. The index convention specifies an order among equal-time jobs. This normalization justifies restricting the dynamic program to ordered interleavings while preserving both feasibility and optimality.
--
--   **Formalization Note.** Each job set is `Fin n`, schedules are duplicate-free lists of all jobs, and the agentwise ordering is a pairwise condition on the list.
-- source:
--   A. Agnetis, P. B. Mirchandani, D. Pacciarelli, and A. Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 229–242 (2004), §9, p. 238, SPT-order observation preceding equation (7), https://doi.org/10.1287/opre.1030.0092. The stated simultaneous weak dominance is the explicit exchange property used to justify that observation.

import Definitions.Def_TwoAgentSched_TotalTotal_DP
set_option autoImplicit false

namespace TwoAgentSched.TotalTotal

/-- Source-grounded exchange obligation: SPT-order each agent without worsening either sum. -/
theorem spt_normalization (I : Instance) (hA : Monotone I.pA) (hB : Monotone I.pB) :
    ∀ l : List (Fin I.nA ⊕ Fin I.nB), MooreLateJobs.Shared.IsSchedule Finset.univ l →
      ∃ σ : List (Fin I.nA ⊕ Fin I.nB),
        MooreLateJobs.Shared.IsSchedule Finset.univ σ ∧
        σ.Pairwise (fun x y => match x, y with
          | Sum.inl a, Sum.inl b => a.val < b.val
          | Sum.inr a, Sum.inr b => a.val < b.val
          | _, _ => True) ∧
        I.sumCA σ ≤ I.sumCA l ∧ I.sumCB σ ≤ I.sumCB l := by
  sorry

end TwoAgentSched.TotalTotal
