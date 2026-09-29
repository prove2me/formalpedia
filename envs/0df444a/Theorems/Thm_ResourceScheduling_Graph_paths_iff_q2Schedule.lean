-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_paths_iff_q2Schedule
-- name    : ResourceScheduling.Graph.paths_iff_q2Schedule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:34:52.768229+00:00
-- url     : https://prove2.me/theorems/41e0b060-3138-482f-8800-e4f73541fb5c
-- title:
--   Proof of Theorem 3 — PARTITION INTO PATHS OF LENGTH 2 has a solution iff C_max ≤ t is feasible on Q2 with speeds 2, 1
-- statement:
--   Let $G=(V,E)$ be a graph with $|V|=3t$, and let $I(G)$ be the scheduling instance constructed from $G$ (one unit-time job per vertex, one unit resource $R_{\{j,k\}}$ per non-adjacent pair $\{j,k\}$, required by $J_j$ and $J_k$), on two uniform machines with speeds $q_1=2$ and $q_2=1$, so that a job takes time $\tfrac12$ on $M_1$ and time $1$ on $M_2$. Then
--   $$V \text{ can be partitioned into } t \text{ triples each spanning a path of length } 2 \text{ in } G\quad\Longleftrightarrow\quad I(G)\ \text{has a feasible schedule with } C_{\max}\le t .$$
--
--   This is the correctness of the reduction from PARTITION INTO PATHS OF LENGTH 2 to $Q2\,|\,res{\cdot}11,\,p_j=1\,|\,C_{\max}$ used in the proof of Theorem 3.
--
--   **Formalization Note.** A triple "spans a path of length 2" when at least two of its three pairs are edges (a triangle qualifies). Machines are indexed from $0$, so the speed vector is $(2,1)$. Schedules have real start times and half-open execution intervals, and the resource constraints are checked at every real time.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 15, proof of Theorem 3

import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Construction

namespace ResourceScheduling.Graph

/-- Proof of Theorem 3, p. 15: a graph with `|V| = 3t` has a partition into paths of length 2 if
and only if the constructed instance on two uniform machines with speeds `q_1 = 2`, `q_2 = 1`
has a feasible schedule with `C_max ≤ t`. -/
theorem paths_iff_q2Schedule (d : GraphData) :
    PartitionIntoPathsOfLength2 d.G ↔
      ((reduce d).toInstance 2 ![2, 1] (by intro i; fin_cases i <;> norm_num)).HasScheduleWithin
        d.t := by sorry

end ResourceScheduling.Graph
