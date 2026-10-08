-- Prove2me | Theorems.Thm_TreewidthApprox_Partition_comp_subset_part
-- name    : TreewidthApprox.Partition.comp_subset_part
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:24.123856+00:00
-- url     : https://prove2.me/theorems/dbd6fc0a-ec61-4724-a3b4-da7863a2ea5b
-- title:
--   Proof of Lemma 2.9 — a component lies in one part
-- statement:
--   Let $M_1,M_2,M_3$ be disjoint vertex sets that cover $V(G)\setminus X$, with no graph edge between distinct parts. Every connected component of $G\setminus X$ that meets $M_i$ lies wholly inside $M_i$, for $i=1,2,3$:
--
--   $$
--   u\in M_i\quad\Longrightarrow\quad C_X(u)\subseteq M_i.
--   $$
--
--   This supplies the component containment used in one direction of Lemma 2.9.
--
--   **Formalization Note** Empty parts are allowed. The three unordered pairs express the paper's condition for all $i\ne j$, using symmetry of a simple graph.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 364, proof of Lemma 2.9, first paragraph, https://doi.org/10.1137/130947374

import Mathlib
import Definitions.Def_TreewidthApprox_Partition_Setting

namespace TreewidthApprox.Partition

/-- Proof of Lemma 2.9, p. 364: when the parts partition `G \ X` with no
cross edges, each component lies wholly in the part containing its starting vertex. -/
theorem comp_subset_part {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X M₁ M₂ M₃ : Finset V)
    (hpart : Disjoint M₁ M₂ ∧ Disjoint M₁ M₃ ∧ Disjoint M₂ M₃ ∧
      M₁ ∪ M₂ ∪ M₃ = Finset.univ \ X)
    (hedge : TreewidthApprox.Pushed.NoEdge G M₁ M₂ ∧ TreewidthApprox.Pushed.NoEdge G M₁ M₃ ∧ TreewidthApprox.Pushed.NoEdge G M₂ M₃) :
    (∀ u ∈ M₁, TreewidthApprox.Pushed.avoidComp G X u ⊆ M₁) ∧
    (∀ u ∈ M₂, TreewidthApprox.Pushed.avoidComp G X u ⊆ M₂) ∧
    (∀ u ∈ M₃, TreewidthApprox.Pushed.avoidComp G X u ⊆ M₃) := by sorry

end TreewidthApprox.Partition
