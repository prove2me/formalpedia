-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Structure_result_11_3
-- name    : RobertsonSeymour1991.GM10.Structure.result_11_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:13:05.987995+00:00
-- url     : https://prove2.me/theorems/2ddd9e36-0f19-4311-98db-f713e0c6e393
-- title:
--   (11.3), p. 186 — tree-decomposition over 𝒮^{3θ−2} ∪ ℛ_{4θ−3} with Z in a node whose Z-extension is in the class
-- statement:
--   Let $\mathcal S$ be a class of designs and $\theta \ge 1$. Let $G$ be a finite hypergraph such that $\mathcal S$ is $\theta$-pervasive in $G$, and let $Z \subseteq V(G)$ with $|Z| \le 3\theta - 2$. Write
--   $$\mathcal S' = \mathcal S^{3\theta-2} \cup \mathcal R_{4\theta-3}.$$
--   Then there is a tree-decomposition $(T, \tau)$ of $G$ over $\mathcal S'$ such that for some $t_0 \in V(T)$, $Z \subseteq V(\tau(t_0))$ and $\mathcal S'$ contains the $Z$-extension of the design of $t_0$ in $(T, \tau)$.
--
--   This is the strengthened form of the structure theorem (11.1), suited to induction on $|V(G)|$; (11.1) is the case $Z = \emptyset$.
--
--   **Formalization Note** Designs are $G$-designs, classes are `Set G.Design`; $\mathcal S^n$ is `enlarge 𝒮 n` and $\mathcal R_n$ is `smallDesigns n`. The tree has vertex set `Fin n` for some $n$. Since $\theta \ge 1$, $3\theta - 2$ and $4\theta - 3$ are exact in $\mathbb N$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 186, (11.3)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_TreeDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_Design

namespace RobertsonSeymour1991.GM10.Structure

theorem result_11_3 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ) (hθ : 1 ≤ θ)
    (𝒮 : Set G.Design) (h𝒮 : Hypergraph.IsPervasive θ 𝒮) (Z : Set V) (hZ : Z.ncard ≤ 3 * θ - 2) :
    ∃ (n : ℕ) (D : TreeDecomposition G n),
      D.IsOver (Hypergraph.enlarge 𝒮 (3 * θ - 2) ∪ G.smallDesigns (4 * θ - 3)) ∧
      ∃ t₀ : Fin n, Z ⊆ (D.τ t₀).verts ∧
        Hypergraph.zExtension (D.nodeDesign t₀) Z ∈
          Hypergraph.enlarge 𝒮 (3 * θ - 2) ∪ G.smallDesigns (4 * θ - 3) := by sorry

end RobertsonSeymour1991.GM10.Structure
