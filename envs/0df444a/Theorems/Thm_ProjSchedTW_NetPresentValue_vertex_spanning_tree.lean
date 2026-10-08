-- Prove2me | Theorems.Thm_ProjSchedTW_NetPresentValue_vertex_spanning_tree
-- name    : ProjSchedTW.NetPresentValue.vertex_spanning_tree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:44:47.743546+00:00
-- url     : https://prove2.me/theorems/e1acd620-ee04-4da5-890e-6fd55068ce14
-- title:
--   Proposition 3.2.16 — each vertex of the time-feasible region is given by a spanning tree of the project network
-- statement:
--   Consider a project whose network $N$ has, for every node $i$, a directed walk from node $0$ to $i$ of nonnegative length; this is the standing convention of §1.2. Let $S$ be a vertex (extreme point) of the time-feasible region $\mathcal S_T$. Then there is a spanning tree $G=\langle V,E^G;\delta^G\rangle$ of $N$, with $E^G\subseteq E$ and weights $\delta^G_{ij}=\delta_{ij}$, such that $S$ is the unique solution of
--   $$S_0=0,\qquad S_j-S_i=\delta_{ij}\quad(\langle i,j\rangle\in E^G).$$
--   If $S$ is moreover a minimal point of $\mathcal S_T$, then $G$ can be chosen to be a spanning outtree of $N$ rooted at node $0$.
--
--   This is the second observation behind Proposition 3.9.2: every vertex schedule comes with at least one spanning tree, on which the subproject net present values are defined.
--
--   **Formalization Note** The standing convention of p. 8 (a path of nonnegative length from $0$ to every node) is a hypothesis, stated with walks. Without it the constraints $S_i\ge0$ can define a vertex that no set of arcs of $N$ describes.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 217, Proposition 3.2.16; standing convention p. 8

import Mathlib
import Definitions.Def_ProjSchedTW_NetPresentValue_Project
import Definitions.Def_ProjSchedTW_NetPresentValue_Trees

namespace ProjSchedTW.NetPresentValue

/-- Proposition 3.2.16 (p. 217). Assume the standing convention of §1.2 (p. 8) that every node
`i` is reached from node `0` by a walk of nonnegative length in `N`. Each vertex `S` of the
time-feasible region `S_T` corresponds to a spanning tree `E^G ⊆ E` of `N`, with weights
`δ_ij`, such that `S` uniquely solves `S_0 = 0`, `S_j − S_i = δ_ij` (`⟨i,j⟩ ∈ E^G`); if `S` is a
minimal point of `S_T`, the tree can be chosen to be a spanning outtree rooted at `0`. -/
theorem vertex_spanning_tree {n : ℕ} (P : Project n)
    (hreach : ∀ i : Fin (n + 2), ∃ w : ℤ, 0 ≤ w ∧ WalkLength P 0 i w)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ (timeFeasibleSet P).extremePoints ℝ) :
    (∃ EG : Finset (Fin (n + 2) × Fin (n + 2)), EG ⊆ P.E ∧ ProjSchedTW.StableSchedules.IsSpanningTree EG ∧
      ProjSchedTW.StableSchedules.UniquelySolves P.δ EG S) ∧
    (Minimal (· ∈ timeFeasibleSet P) S →
      ∃ EG : Finset (Fin (n + 2) × Fin (n + 2)), EG ⊆ P.E ∧ ProjSchedTW.StableSchedules.IsSpanningOuttree 0 EG ∧
        ProjSchedTW.StableSchedules.UniquelySolves P.δ EG S) := by sorry

end ProjSchedTW.NetPresentValue
