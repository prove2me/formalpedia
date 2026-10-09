-- Prove2me | Theorems.Thm_PlanarQueue_Planar_theorem_15
-- name    : PlanarQueue.Planar.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:24:53.093439+00:00
-- url     : https://prove2.me/theorems/8100c3d9-abdb-4d96-b73a-41e6c288bcab
-- title:
--   Theorem 15 — planar layered partition of width three
-- statement:
--   Let $G$ be any finite planar graph and fix any BFS layering $(V_0,V_1,\ldots)$ of $G$. There is a partition $\mathcal P$ of its vertices such that each part meets each layer in at most three vertices, while the quotient $G/\mathcal P$ is planar and has treewidth at most three:
--
--   $$
--   |A\cap V_i|\le 3\quad(A\in\mathcal P,\ i\ge0),
--   \qquad
--   G/\mathcal P\text{ is planar},
--   \qquad
--   \operatorname{tw}(G/\mathcal P)\le3.
--   $$
--
--   The universal choice of BFS layering states the theorem's “Moreover” clause and supplies the structural input to the 49-queue bound.
--
--   **Formalization Note** A BFS layering chooses one root per component, including when $G$ is disconnected. The partition has nonempty parts, and the quotient uses exactly those parts.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, p. 16, Theorem 15

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting

namespace PlanarQueue.Planar

/-- Theorem 15: the width-three partition exists for each BFS layering. -/
theorem theorem_15 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsPlanar G)
    (L : V → ℕ) (hL : IsBFSLayering G L) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ A ∈ P.parts, ∀ i : ℕ,
        (A.filter fun v => L v = i).card ≤ 3) ∧
      IsPlanar (quotientGraph G P) ∧
      RobertsonSeymour1986.GM5.TreewidthLE (quotientGraph G P) 3 := by sorry

end PlanarQueue.Planar
