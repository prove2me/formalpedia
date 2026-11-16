-- Prove2me | Theorems.Thm_TangleStructTree_Supplement_theorem_7_1
-- name    : TangleStructTree.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:14:21.233806+00:00
-- url     : https://prove2.me/theorems/db27d081-1ab9-48b5-8182-6d7e7defe9d4
-- title:
--   Theorem 7.1 — a $k$-block or a $\mathcal B_k$-tree of $\vec S_k$, exactly one
-- statement:
--   Let $G$ be a finite graph, $S$ the set of its separations with the usual order function $|(A,B)|=|A\cap B|$, and $k\in\mathbb N$. Put
--   $$\mathcal B_k=\Big\{\sigma\subseteq\vec S:\ \Big|\bigcap\{B:(A,B)\in\sigma\}\Big|<k\Big\}.$$
--   Then exactly one of the following holds:
--
--   1. $G$ has a $k$-block;
--   2. there exists a $\mathcal B_k$-tree of $\vec S_k$.
--
--   In the case of (2), the $\mathcal B_k$-tree can be chosen to be irreducible, efficient and ordered.
--
--   This gives explicit, checkable certificates for the non-existence of $k$-blocks, which tangle-tree duality for stars does not provide since $\mathcal B_k$ does not consist of stars.
--
--   Differences from the source:
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
--   - encoding: exactly one of (i), (ii) holds; in the case of (ii) the tree can be chosen with further properties → (i) ↔ ¬ (ii), and (ii) → ∃ one tree with all the properties together; reason: "exactly one" is (i) or (ii) but not both; the chosen tree is a single tree
--   - encoding: a graph G → a finite simple graph (SimpleGraph V, Fintype V); reason: the paper adopts the terminology of [11], in which graphs are finite; loops and parallel edges do not affect separations or k-blocks
--   - encoding: the set S of separations (A, B) of G with (A′, B′) ≤ (A, B) iff A′ ⊇ A, B′ ⊆ B, and (A, B)∗ = (B, A) → GraphSep G: pairs of Finsets satisfying RobertsonSeymour1986_GM5_IsSeparation, with that order and involution; reason: the published separation definition is [11]'s; the order is the paper's footnote 24
--   - encoding: S⃗_k = {s⃗ ∈ S⃗ : |s| < k} → the subtype Sk ord k = {x // ord x < k ∧ ord (x∗) < k} with the induced order, involution and order function; reason: for an order function both conditions say |s| < k, so it is the same set; the second makes the subtype closed under ∗ without a hypothesis
--   - encoding: B_k as a set of subsets of S⃗ → Bk G k on S⃗_k, with |⋂ B| as Set.ncard and the intersection over σ = ∅ equal to V; reason: only subsets of S⃗_k matter for B_k-trees of S⃗_k; the empty intersection is V by convention
--   - encoding: k-block: a maximal set of at least k vertices no two of which can be separated by < k vertices → IsKBlock: |X| ≥ k, no two distinct vertices of X separated by any Z with |Z| < k (a, b ∉ Z, every a–b walk meets Z), and maximal with these properties; reason: separation of vertices as in [11]; every walk contains a path
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Theorem 7.1, p.21 (PDF 32); = extended abstract Theorem 7.1, p.9; order of graph separations, footnote 24, p.22 (PDF 33)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_Supplement_Sk
import Definitions.Def_TangleStructTree_Supplement_GraphSep
import Definitions.Def_TangleStructTree_Supplement_Bk
import Definitions.Def_TangleStructTree_Supplement_IsKBlock
import Definitions.Def_TangleStructTree_Supplement_IsFTree
import Definitions.Def_TangleStructTree_Supplement_IsEfficientTree
import Definitions.Def_TangleStructTree_Supplement_IsIrreducible
import Definitions.Def_TangleStructTree_Supplement_IsOrderedTree

namespace TangleStructTree

namespace Supplement

/-- **Theorem 7.1** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version (Part I), p.21 (PDF 32); = extended abstract Theorem 7.1, p.9). Let `S` be the set
of separations of a graph `G`, with the usual order function [11], and let `k ∈ ℕ`. Then exactly
one of the following assertions holds:
(i) `G` has a `k`-block;
(ii) there exists a `B_k`-tree of `S⃗_k`.
In the case of (ii), the `B_k`-tree can be chosen to be irreducible, efficient, and ordered.

**Formalization Note**
1. `G` is a finite simple graph (`Fintype V`), the convention of [11] adopted by the paper.
2. `S⃗` is `GraphSep G` (all separations `(A, B)`), with the paper's order (footnote 24, p.22):
   `(A′, B′) ≤ (A, B)` iff `A′ ⊇ A` and `B′ ⊆ B`, and `(A, B)∗ = (B, A)`. The usual order function
   is `|(A, B)| = |A ∩ B|` (`sepOrder G`); `S⃗_k` is `Sk (sepOrder G) k` with the order function
   `x ↦ |A ∩ B|` restricted to it.
3. `B_k = {σ ⊆ S⃗_k : |⋂{B : (A, B) ∈ σ}| < k}` (`Bk G k`), the intersection over `σ = ∅` being `V`.
4. "Exactly one" is `(i) ↔ ¬ (ii)`; "chosen to be irreducible, efficient, and ordered" is one tree
   with all these properties together, given (ii). -/
theorem theorem_7_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) :
    ((∃ X : Finset V, IsKBlock G k X) ↔
        ¬ ∃ T : SepTree (Sk (sepOrder G) (k : ℝ)), IsFTree T (Bk G k)) ∧
      ((∃ T : SepTree (Sk (sepOrder G) (k : ℝ)), IsFTree T (Bk G k)) →
        ∃ T : SepTree (Sk (sepOrder G) (k : ℝ)), IsFTree T (Bk G k) ∧ IsIrreducible T (Bk G k) ∧
          IsEfficientTree T (fun x => sepOrder G x.1) ∧
          IsOrderedTree T (fun x => sepOrder G x.1)) := by sorry

end Supplement

end TangleStructTree
