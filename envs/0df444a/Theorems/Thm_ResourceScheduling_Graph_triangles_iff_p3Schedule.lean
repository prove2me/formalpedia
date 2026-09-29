-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_triangles_iff_p3Schedule
-- name    : ResourceScheduling.Graph.triangles_iff_p3Schedule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:31:42.114152+00:00
-- url     : https://prove2.me/theorems/086f2773-e167-47dd-868a-09c9d4f4214a
-- title:
--   Proof of Theorem 2 — PARTITION INTO TRIANGLES has a solution iff C_max ≤ t is feasible on P3
-- statement:
--   Let $G=(V,E)$ be a graph with $|V|=3t$, and let $I(G)$ be the scheduling instance constructed from $G$ (one unit-time job per vertex, one unit resource $R_{\{j,k\}}$ per non-adjacent pair $\{j,k\}$, required by $J_j$ and $J_k$), on three identical machines. Then
--   $$V \text{ can be partitioned into } t \text{ triangles of } G\quad\Longleftrightarrow\quad I(G)\ \text{has a feasible schedule with } C_{\max}\le t .$$
--
--   This is the correctness of the reduction from PARTITION INTO TRIANGLES to $P3\,|\,res{\cdot}11,\,p_j=1\,|\,C_{\max}$ used in the proof of Theorem 2.
--
--   **Formalization Note.** Schedules have real start times, half-open execution intervals, and the resource constraints are checked at every real time.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 15, proof of Theorem 2

import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Construction

namespace ResourceScheduling.Graph

/-- Proof of Theorem 2, p. 15: a graph with `|V| = 3t` has a partition into triangles if and
only if the constructed instance on three identical machines has a feasible schedule with
`C_max ≤ t`. -/
theorem triangles_iff_p3Schedule (d : GraphData) :
    PartitionIntoTriangles d.G ↔
      ((reduce d).toInstance 3 (fun _ => 1) (fun _ => one_pos)).HasScheduleWithin d.t := by sorry

end ResourceScheduling.Graph
