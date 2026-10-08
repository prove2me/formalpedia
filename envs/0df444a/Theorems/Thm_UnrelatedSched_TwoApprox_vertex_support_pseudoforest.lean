-- Prove2me | Theorems.Thm_UnrelatedSched_TwoApprox_vertex_support_pseudoforest
-- name    : UnrelatedSched.TwoApprox.vertex_support_pseudoforest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:16:45.075755+00:00
-- url     : https://prove2.me/theorems/3b6fa3be-aab6-4c66-ae47-0456cc619728
-- title:
--   §2, proof of Theorem 1, p. 4 — the support graph of a vertex of (LP) is a pseudoforest
-- statement:
--   Let $P=(p_{ij})\in\mathbb N^{m\times n}$, deadlines $d_1,\dots,d_m\in\mathbb R$ and $t\in\mathbb R$, and let $\tilde x$ be a vertex of the linear program (LP) of the Rounding Theorem. Let $G=(M,J,E)$ be the bipartite support graph of $\tilde x$, with $E=\{(i,j)\mid\tilde x_{ij}>0\}$. Then $G$ is a pseudoforest: for every set $S$ of machines and every set $T$ of jobs,
--   $$\big|\{(i,j)\in E : i\in S,\ j\in T\}\big| \le |S|+|T| .$$
--
--   Equivalently, each connected component of $G$ is a tree or a tree plus one edge. This structural fact is what makes the vertex roundable: the rounding of the Rounding Theorem is a matching in this graph.
--
--   **Formalization Note** The paper states the component form ("the number of nodes in each component is at least equal to the number of edges"); the hereditary counting form above is equivalent for finite graphs. The paper's deadlines and threshold are integers; the statement is for real ones, which the proof allows.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 4, §2, proof of Theorem 1

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

/-- §2, proof of Theorem 1, p. 4: the support graph of a vertex of (LP) is a pseudoforest. -/
theorem vertex_support_pseudoforest {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : Fin m → ℝ)
    (t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ) (hx : IsLPVertex P d t x) :
    IsPseudoforest (supportEdges x) := by sorry

end UnrelatedSched.TwoApprox
