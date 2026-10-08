-- Prove2me | Theorems.Thm_TreewidthApprox_Partition_lemma_2_9
-- name    : TreewidthApprox.Partition.lemma_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:29.53478+00:00
-- url     : https://prove2.me/theorems/1a635182-8a89-449e-beb3-98ef5e835c8c
-- title:
--   Lemma 2.9 — balanced S-separators and three non-adjacent parts
-- statement:
--   Let $G$ be a finite simple graph, $S\subseteq V(G)$, and $X\subseteq V(G)$. The set $X$ is a balanced $S$-separator exactly when $V(G)\setminus X$ has a partition into three sets $M_1,M_2,M_3$ such that distinct parts have no edges between them and each part contains at most half the vertices of $S$:
--
--   $$
--   X\text{ is balanced for }S\quad\Longleftrightarrow\quad
--   \exists\,M_1,M_2,M_3:\quad V(G)\setminus X=M_1\mathbin{\dot\cup}M_2\mathbin{\dot\cup}M_3,
--   \quad\operatorname{NoEdge}_G(M_i,M_j)\ (i\ne j),
--   \quad 2|M_i\cap S|\le |S|\ (i=1,2,3).
--   $$
--
--   The equivalence replaces a condition on every connected component by conditions on three vertex sets.
--
--   **Formalization Note** Parts may be empty; in particular, $X=V(G)$ is included. The three unordered pairs suffice because adjacency is symmetric. Cardinality bounds use natural numbers with denominators cleared, and $S$ retains its full cardinality even when it meets $X$. The component relation uses walks avoiding $X$ at every vertex. No bound on $|X|$ or treewidth is assumed. Lean uses a vertex type in universe 0, consistently with this series.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 328, Lemma 2.9 (restated as Lemma 6.2, p. 363), https://doi.org/10.1137/130947374

import Mathlib
import Definitions.Def_TreewidthApprox_Partition_Setting

namespace TreewidthApprox.Partition

/-- Lemma 2.9, p. 328 (restated as Lemma 6.2, p. 363). -/
theorem lemma_2_9 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S X : Finset V) :
    IsBalancedSSep G S X ↔
      ∃ M₁ M₂ M₃ : Finset V,
        Disjoint M₁ M₂ ∧ Disjoint M₁ M₃ ∧ Disjoint M₂ M₃ ∧
        M₁ ∪ M₂ ∪ M₃ = Finset.univ \ X ∧
        TreewidthApprox.Pushed.NoEdge G M₁ M₂ ∧ TreewidthApprox.Pushed.NoEdge G M₁ M₃ ∧ TreewidthApprox.Pushed.NoEdge G M₂ M₃ ∧
        2 * (M₁ ∩ S).card ≤ S.card ∧
        2 * (M₂ ∩ S).card ≤ S.card ∧
        2 * (M₃ ∩ S).card ≤ S.card := by sorry

end TreewidthApprox.Partition
