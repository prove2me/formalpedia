-- Prove2me | Theorems.Thm_TwoAgentSched_LateLate_lemma_7_1
-- name    : TwoAgentSched.LateLate.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:41.132064+00:00
-- url     : https://prove2.me/theorems/6a04b215-7276-4c13-8690-25d16fc2273b
-- title:
--   Lemma 7.1 — some optimal schedule has its early jobs first, in EDD order, and its late jobs last
-- statement:
--   Consider the problem $1\|\sum U^A_i : \sum U^B_i \le Q$: jobs $J_1,\dots,J_n$ owned by agents $A$ and $B$, with processing times $p_j$ and due dates $d_j$, are sequenced on one machine from time $0$ without idle time; at most $Q$ jobs of $B$ may be late, and the number of late jobs of $A$ is minimized. Suppose the instance is feasible, i.e. some sequence has at most $Q$ late $B$-jobs. Then there is an optimal sequence $\sigma^*$ and an index $m$ such that
--
--   1. the jobs in the first $m$ positions of $\sigma^*$ are exactly its early jobs, and the jobs in positions $m+1, \dots, n$ are exactly its late jobs;
--   2. the early jobs appear in earliest-due-date order:
--   $$d_{\sigma^*(1)} \le d_{\sigma^*(2)} \le \dots \le d_{\sigma^*(m)}.$$
--
--   The order of the late jobs is arbitrary. This structural lemma reduces the search for an optimal schedule to the choice of the set of early jobs, which is what the dynamic program of §7 enumerates.
--
--   **Formalization Note** The feasibility hypothesis is added: without a feasible sequence there is no optimal one, and the paper's "there is an optimal schedule" presupposes one. Positions are 0-based in Lean; job $j$ at position $k$ is early iff its completion time `completionAt p l k` is at most $d_j$. EDD order allows ties.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 236, Lemma 7.1

import Mathlib
import Definitions.Def_TwoAgentSched_LateLate_Model

namespace TwoAgentSched.LateLate

/-- Lemma 7.1 (p. 236). If `1‖ΣU^A_i : ΣU^B_i ≤ Q` has a feasible sequence, it has an optimal
sequence `l` whose first `m` jobs are exactly its early jobs (every job at a position `< m` meets
its due date, every job at a position `≥ m` is late) and whose early jobs are in EDD order
(nondecreasing due dates). -/
theorem lemma_7_1 {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) (Q : ℕ)
    (hfeas : ∃ l : List (Fin n), IsFeasible p d ag Q l) :
    ∃ l : List (Fin n), IsOptimal p d ag Q l ∧
      ∃ m ≤ l.length,
        (∀ (k : ℕ) (hk : k < l.length),
          (k < m ↔ MooreLateJobs.Shared.completionAt (fun j => (p j : ℝ)) l k ≤ (d l[k] : ℝ))) ∧
        (l.take m).Pairwise (fun a b => d a ≤ d b) := by sorry

end TwoAgentSched.LateLate
