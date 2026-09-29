-- Prove2me | Theorems.Thm_ResourceScheduling_Chain_threePartition_iff_p3Schedule
-- name    : ResourceScheduling.Chain.threePartition_iff_p3Schedule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:25:44.990561+00:00
-- url     : https://prove2.me/theorems/5d594357-75a5-426a-b3d3-7db7f8f428f0
-- title:
--   Proof of Theorem 4 — under saturation, $P3\mid res1\cdot\cdot, p_j=1\mid C_{\max}$ is equivalent to 3-PARTITION
-- statement:
--   Let $t \in \mathbb{N}$, let $b$ be a positive integer and $a_1,\dots,a_{3t}$ positive integers with $\sum_{j=1}^{3t} a_j = tb$. Consider the instance of $P3\mid res1\cdot\cdot, p_j = 1\mid C_{\max}$ with $3t$ unit-time jobs $J_1,\dots,J_{3t}$, three identical machines, one resource of size $b$, requirements $r_{1j} = a_j$ and no precedence constraints. Then
--   $$\{1,\dots,3t\} \text{ can be partitioned into } t \text{ disjoint 3-element sets } S_i \text{ with } \sum_{j\in S_i} a_j = b \iff \text{some feasible schedule has } C_{\max} \le t.$$
--
--   With $3t$ unit jobs on three machines in time $t$, and total requirement $tb$ against a resource of size $b$, both the machines and the resource are saturated; this is the paper's statement "When the machines and resources are all saturated, $P3\mid res1\cdot\cdot, p_j = 1\mid C_{\max}$ is equivalent to the following problem: 3-PARTITION". It is the reduction behind Theorem 4.
--
--   **Formalization Note.** Schedules have real start times and the resource constraint is checked at every real time. The page's version of 3-PARTITION has no bounds on the $a_j$, so none are assumed here.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 16, proof of Theorem 4

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Constructions

namespace ResourceScheduling.Chain
theorem threePartition_iff_p3Schedule (P : ThreePartition) (hb : 0 < P.b)
    (ha : ∀ j, 0 < P.a j) (hsum : ∑ j, P.a j = P.t * P.b) :
    P.HasSolution ↔ P.p3Instance.HasScheduleWithin P.t := by sorry
end ResourceScheduling.Chain
