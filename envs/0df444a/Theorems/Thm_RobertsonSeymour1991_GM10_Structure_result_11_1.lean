-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Structure_result_11_1
-- name    : RobertsonSeymour1991.GM10.Structure.result_11_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:13:11.126365+00:00
-- url     : https://prove2.me/theorems/57990a33-9c7d-4470-92f3-cdceb8d366b7
-- title:
--   (11.1), p. 185 — a θ-pervasive class 𝒮 gives a tree-decomposition over 𝒮^{3θ−2} ∪ ℛ_{4θ−3}
-- statement:
--   Let $G$ be a finite hypergraph, let $\theta \ge 1$, and let $\mathcal S$ be a class of designs which is $\theta$-pervasive in $G$: for every subhypergraph $G'$ of $G$ and every tangle $\mathcal T$ in $G'$ of order $\ge \theta$, some location $\mathcal L \subseteq \mathcal T$ in $G'$ has its design in $\mathcal S$. Then $G$ has a tree-decomposition over
--   $$\mathcal S^{3\theta-2} \cup \mathcal R_{4\theta-3},$$
--   that is, the design of every node is either a $(3\theta-2)$-enlargement of a member of $\mathcal S$ or has at most $4\theta - 3$ vertices.
--
--   This is the main structure theorem of §11: local structure relative to every high-order tangle yields a global tree-decomposition into pieces that almost have that structure. With $\mathcal S = \emptyset$ it recovers a bound of the form $\omega(G) \le 4\theta(G)$ on tree-width.
--
--   **Formalization Note** Designs are encoded as $G$-designs (pairs of a subhypergraph of $G$ and a set of vertex sets) and a class of designs as a set of them; see the Design definition. $\mathcal S^n$ is `enlarge 𝒮 n`, $\mathcal R_n$ is `smallDesigns n`, and "over" is `IsOver`. Since $\theta \ge 1$, $3\theta - 2$ and $4\theta - 3$ are exact in $\mathbb N$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 185, (11.1)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_TreeDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_Design

namespace RobertsonSeymour1991.GM10.Structure

theorem result_11_1 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ) (hθ : 1 ≤ θ)
    (𝒮 : Set G.Design) (h𝒮 : Hypergraph.IsPervasive θ 𝒮) :
    ∃ (n : ℕ) (D : TreeDecomposition G n),
      D.IsOver (Hypergraph.enlarge 𝒮 (3 * θ - 2) ∪ G.smallDesigns (4 * θ - 3)) := by sorry

end RobertsonSeymour1991.GM10.Structure
