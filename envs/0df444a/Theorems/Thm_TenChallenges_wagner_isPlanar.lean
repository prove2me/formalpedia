-- Prove2me | Theorems.Thm_TenChallenges_wagner_isPlanar
-- name    : TenChallenges.wagner_isPlanar
-- status  : Open
-- author  : @Davide
-- created : 2026-11-18T12:23:44.899135+00:00
-- url     : https://prove2.me/theorems/516ae02a-7294-4d9a-9ae5-ee8568bf833d
-- title:
--   Wagner's theorem: no $K_5$ or $K_{3,3}$ minor implies a plane drawing
-- statement:
--   **Wagner's theorem (hard direction).** Let $G$ be a finite simple graph that has neither the complete graph $K_5$ nor the complete bipartite graph $K_{3,3}$ as a minor. Then $G$ is planar: it has a drawing in the plane $\mathbb R^2$ in which the vertices are distinct points, every edge is a simple arc joining its ends and avoiding all other vertices, and two distinct edges meet only at common endpoints.
--
--   $$K_5\not\preceq G\ \text{ and }\ K_{3,3}\not\preceq G\quad\Longrightarrow\quad G\ \text{is planar}.$$
--
--   This is the nontrivial half of Wagner's characterisation of planar graphs by excluded minors, the minor version of Kuratowski's theorem. It connects the combinatorial planarity notion used in the Ten Challenges 06 statement (Wagner's criterion) with the topological notion used in Graph Minors V.
--
--   **Formalization Note** The hypothesis is `IsWagnerPlanar` (no $K_5$ and no $K_{3,3}$ minor, branch-set model). The conclusion is `IsPlanar` from Graph Minors V: a `PlaneDrawing` by simple arcs.
-- source:
--   K. Wagner, Über eine Eigenschaft der ebenen Komplexe, Math. Ann. 114 (1937), 570–590 (characterisation of planar graphs by the excluded minors K_5 and K_{3,3}); equivalently Kuratowski, Fund. Math. 15 (1930), 271–283, combined with the fact that a K_5- or K_{3,3}-minor yields a K_5- or K_{3,3}-subdivision.

import Definitions.Def_TenChallenges_Minor
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace TenChallenges
theorem wagner_isPlanar {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsWagnerPlanar) :
    RobertsonSeymour1986.GM5.IsPlanar G := by sorry
end TenChallenges
