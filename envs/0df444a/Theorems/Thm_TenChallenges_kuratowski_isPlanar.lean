-- Prove2me | Theorems.Thm_TenChallenges_kuratowski_isPlanar
-- name    : TenChallenges.kuratowski_isPlanar
-- status  : Open
-- author  : @Davide
-- created : 2026-11-18T12:40:10.776452+00:00
-- url     : https://prove2.me/theorems/eebf2191-651a-4011-bceb-422efeb43da1
-- title:
--   Kuratowski's theorem: no $K_5$ or $K_{3,3}$ subdivision implies a plane drawing
-- statement:
--   **Kuratowski's theorem (hard direction).** Let $G$ be a finite simple graph that contains no subdivision of $K_5$ and no subdivision of $K_{3,3}$. Then $G$ is planar: it has a drawing in $\mathbb R^2$ in which vertices are distinct points, each edge is a simple arc between its ends avoiding all other vertices, and distinct edges meet only at common endpoints.
--
--   $$K_5\not\preceq_{\mathrm{top}} G\ \text{ and }\ K_{3,3}\not\preceq_{\mathrm{top}} G\quad\Longrightarrow\quad G\ \text{is planar}.$$
--
--   Together with the fact that topological minors are minors, it implies Wagner's theorem that graphs with no $K_5$ or $K_{3,3}$ minor are planar.
--
--   **Formalization Note** Containing a subdivision is `SimpleGraph.TopologicalMinor`; planarity is `IsPlanar` from Graph Minors V (a `PlaneDrawing` by simple arcs).
-- source:
--   K. Kuratowski, Sur le problème des courbes gauches en topologie, Fund. Math. 15 (1930), 271–283: a finite graph is planar if and only if it contains no subgraph homeomorphic to K_5 or K_{3,3}.

import Definitions.Def_TenChallenges_Minor
import Definitions.Def_TenChallenges_TopologicalMinor
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace TenChallenges
theorem kuratowski_isPlanar {V : Type} [Fintype V] (G : SimpleGraph V)
    (h5 : ¬ Nonempty (SimpleGraph.TopologicalMinor SimpleGraph.K5 G))
    (h33 : ¬ Nonempty (SimpleGraph.TopologicalMinor SimpleGraph.K33 G)) :
    RobertsonSeymour1986.GM5.IsPlanar G := by sorry
end TenChallenges
