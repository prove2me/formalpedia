-- Prove2me | Theorems.Thm_PlanarQueue_Genus_theorem_2
-- name    : PlanarQueue.Genus.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:25:14.812196+00:00
-- url     : https://prove2.me/theorems/2de08a18-23a4-4c3f-a0e8-0d8742716826
-- title:
--   Theorem 2 — every graph of Euler genus g has queue-number at most 4g + 49
-- statement:
--   **Theorem 2** (Dujmović, Joret, Micek, Morin, Ueckerdt, Wood). Let $g \ge 0$ and let $G$ be a finite graph of Euler genus at most $g$. Then
--   $$\operatorname{qn}(G) \le 4g + 49.$$
--
--   The paper states Theorem 2 as "queue-number at most $O(g)$" and proves the explicit bound $4g + 49$ (p. 5 and §5, pp. 22–23). It extends Theorem 1 (planar graphs, the case $g = 0$, with bound $49$) to all surfaces, orientable or not.
--
--   **Formalization Note** "Euler genus $g$" is read as "Euler genus at most $g$"; since $4g + 49$ is increasing in $g$ this is equivalent. Euler genus is the combinatorial embedding-scheme notion (rotation system and edge signature, Mohar–Thomassen §3.3), which equals the topological Euler genus of the paper's footnote 2. The explicit constant $4g + 49$ replaces "$O(g)$"; it is the paper's own bound, so the statement is the paper's strongest form. $G$ need not be connected. "$\operatorname{qn}(G) \le k$" is the existence of an injective vertex order and an assignment of the edges of $G$ to $k$ queues with no two nested edges in a queue.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, p. 5, Theorem 2 (bound 4g + 49: p. 5 and §5, pp. 22–23, Proof of Theorem 2 with a 4g + 49 upper bound)

import Mathlib
import Definitions.Def_PlanarQueue_Genus_Setting
import Definitions.Def_PlanarQueue_Genus_EulerGenus

namespace PlanarQueue.Genus

/-- Theorem 2 (p. 5) with the bound `4g + 49` (pp. 5, 22–23): every graph of Euler genus at most `g`
has a `(4g + 49)`-queue layout. -/
theorem theorem_2 (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (g : ℕ) (hG : EulerGenusLE G g) : PlanarQueue.Planar.HasQueueLayout G (4 * g + 49) := by sorry

end PlanarQueue.Genus
