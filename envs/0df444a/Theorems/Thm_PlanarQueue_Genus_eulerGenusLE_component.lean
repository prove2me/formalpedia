-- Prove2me | Theorems.Thm_PlanarQueue_Genus_eulerGenusLE_component
-- name    : PlanarQueue.Genus.eulerGenusLE_component
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-30T14:12:28.89829+00:00
-- url     : https://prove2.me/theorems/32cf77ac-dc76-4215-8835-5798e48319a4
-- title:
--   A connected component of a graph of Euler genus at most $g$ has Euler genus at most $g$
-- statement:
--   Let $G$ be a finite graph of Euler genus at most $g$ (in the embedding-scheme sense of `EulerGenusLE`), and let $C$ be a connected component of $G$. Then the subgraph $G[C]$ induced by the vertex set of $C$ also has Euler genus at most $g$:
--   $$\operatorname{eg}(G) \le g \;\Longrightarrow\; \operatorname{eg}(G[C]) \le g .$$
--
--   Role: this justifies the reduction "We may assume that $G$ is connected" at the start of the proof of Theorem 2 (p. 22): the queue layouts of the components are concatenated, and each component must satisfy the genus hypothesis so that Lemma 21 (which assumes $G$ connected) applies to it.
--
--   **Formalization Note**: Euler genus is the combinatorial notion `EulerGenusLE` of `Definitions.Def_PlanarQueue_Genus_EulerGenus` (an embedding scheme, i.e. rotation system plus edge signature, Mohar–Thomassen §3.3, whose Euler genus $2c-n+m-f$ is at most $g$). The finiteness and decidability instances on the component are taken as instance arguments.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, https://arxiv.org/abs/1904.04791, p. 22, Proof of Theorem 2 with a 4g + 49 upper bound ('We may assume that G is connected'); embedding schemes and Euler genus: Mohar–Thomassen, Graphs on Surfaces (2001), §3.3

import Mathlib
import Definitions.Def_PlanarQueue_Genus_EulerGenus

namespace PlanarQueue.Genus

theorem eulerGenusLE_component (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (g : ℕ) (hG : EulerGenusLE G g) (c : G.ConnectedComponent)
    [Fintype c.supp] [DecidableRel (G.induce c.supp).Adj] :
    EulerGenusLE (G.induce c.supp) g := by sorry

end PlanarQueue.Genus
