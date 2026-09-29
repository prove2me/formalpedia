-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_excluding_planar_graph
-- name    : RobertsonSeymour1986.GM5.excluding_planar_graph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:07:03.464211+00:00
-- url     : https://prove2.me/theorems/1900c081-f284-4d50-a70e-32650ff3abf8
-- title:
--   (2.1) Excluding a planar graph: tree-width at most $\theta_9(\theta(H))$
-- statement:
--   Let $H$ be a finite planar graph, and let $\theta(H)$ be the smallest even integer $\theta\ge 6$ such that $H$ is isomorphic to a minor of the $\theta$-grid. Then every finite graph $G$ with no minor isomorphic to $H$ satisfies
--
--   $$\operatorname{tw}(G)\le\theta_9\bigl(\theta(H)\bigr),$$
--
--   where $\theta_9(\theta)=\theta_7(\theta_8+1)+1$ is the explicit parameter of Section 2.
--
--   This is the Excluded Grid Theorem of Robertson and Seymour in its explicit form. Excluding any fixed planar graph bounds the tree-width, while excluding a non-planar graph does not, since the grids have unbounded tree-width. It is the paper's headline result (1.5) with the bound made explicit.
--
--   **Formalization Note** $\theta(H)$ enters as a number $\theta$ assumed to be the least element of $\{t : t \text{ even},\ t\ge 6,\ H \text{ is a minor of the } t\text{-grid}\}$; for planar $H$ this set is nonempty (milestone "Sect. 2"), so the hypothesis is satisfiable. The paper's graphs may have loops and multiple edges, while here $G$ and $H$ are simple. For $G$ this loses nothing, since tree-width and minor containment depend only on adjacency. For $H$ it is a specialization to simple planar graphs.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (2.1), p. 95 (PDF p. 4), with θ(H) as defined on p. 94 (PDF p. 3); explicit form of (1.5), p. 93; DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor
import Definitions.Def_RobertsonSeymour1986_GM5_grid
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_RobertsonSeymour1986_GM5_Params
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace RobertsonSeymour1986.GM5

/-- (2.1), Excluding a planar graph: if `H` is planar, every graph with no minor isomorphic to `H`
has tree-width at most `θ₉(θ(H))`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (2.1), p. 95 (PDF p. 4): "If H is a planar graph, then every graph with no minor isomorphic
to H has tree-width at most θ₉(θ(H))." Here (Sect. 2, p. 94, PDF p. 3) "For any planar graph H there
is an even value of θ ≥ 6 such that H is isomorphic to a minor of the θ-grid. … Denote by θ(H) the
smallest such value of θ." This is the explicit form of the paper's headline result (1.5), p. 93.

**Formalization Note** `θ(H)` is named by the hypothesis `IsLeast {t | Even t ∧ 6 ≤ t ∧
IsMinor H (grid t)} θ` (no junk value; the set is nonempty for planar `H` by the milestone
`planar_isMinor_grid`, so the theorem is not vacuous). `G` ranges over every finite simple graph.
The paper's graphs may have loops and multiple edges. For `G` this changes nothing: tree-width and
minor containment of a simple graph depend only on adjacency. For `H` it is a specialization:
here `H` is a finite simple planar graph. "Minor isomorphic to `H`" is `IsMinor H G`
(branch-set model). Planarity `IsPlanar` mirrors the platform's `FourColor.IsPlanar`. -/
theorem excluding_planar_graph {W : Type} [Fintype W] (H : SimpleGraph W) (hH : IsPlanar H)
    (θ : ℕ) (hθ : IsLeast {t : ℕ | Even t ∧ 6 ≤ t ∧ IsMinor H (grid t)} θ)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : ¬ IsMinor H G) :
    TreewidthLE G (theta9 θ) := by sorry

end RobertsonSeymour1986.GM5
