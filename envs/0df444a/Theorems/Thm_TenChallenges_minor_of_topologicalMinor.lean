-- Prove2me | Theorems.Thm_TenChallenges_minor_of_topologicalMinor
-- name    : TenChallenges.minor_of_topologicalMinor
-- status  : Proved
-- author  : @Davide
-- created : 2026-11-18T12:39:53.508735+00:00
-- url     : https://prove2.me/theorems/2ea60f7e-5389-4521-a478-3b19eb12019b
-- title:
--   A topological minor is a minor
-- statement:
--   If a graph $G$ contains a subdivision of a graph $H$, then $H$ is a minor of $G$:
--
--   $$H\preceq_{\mathrm{top}} G\quad\Longrightarrow\quad H\preceq G.$$
--
--   Each branch vertex together with suitable interior vertices of its incident subdivided edges forms a connected branch set; contracting these recovers $H$. This is the easy comparison between the two containment relations, used to pass from Kuratowski's theorem (excluded subdivisions) to Wagner's theorem (excluded minors).
--
--   **Formalization Note** Subdivisions are `SimpleGraph.TopologicalMinor` and minors are `SimpleGraph.Minor` (branch-set model), for arbitrary vertex types.
-- source:
--   Standard; see e.g. Diestel, Graph Theory, Sect. 1.7 (every topological minor is a minor). Used in deriving Wagner's theorem (Math. Ann. 114 (1937)) from Kuratowski's theorem (Fund. Math. 15 (1930)).

import Definitions.Def_TenChallenges_Minor
import Definitions.Def_TenChallenges_TopologicalMinor

namespace TenChallenges
theorem minor_of_topologicalMinor {W V : Type} {H : SimpleGraph W} {G : SimpleGraph V}
    (T : SimpleGraph.TopologicalMinor H G) : Nonempty (SimpleGraph.Minor H G) := by sorry
end TenChallenges
