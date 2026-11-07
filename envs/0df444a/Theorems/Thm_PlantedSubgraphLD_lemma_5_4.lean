-- Prove2me | Theorems.Thm_PlantedSubgraphLD_lemma_5_4
-- name    : PlantedSubgraphLD.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:18:37.66532+00:00
-- url     : https://prove2.me/theorems/4ff7c3b7-dfa8-4f31-93a4-bf2ca236778c
-- title:
--   Lemma 5.4 — partitioning a subcubic $\{0,1\}$-weighted tree into connected clusters of weight in $[\ell,3\ell]$
-- statement:
--   Let $T$ be a finite tree of maximum degree at most $3$ whose vertices have weights in $\{0,1\}$, with total weight $t$. For every integer $\ell\ge1$ with $t\ge\ell$ there is a partition
--
--   $$
--   V(T)=C_1\sqcup C_2\sqcup\cdots\sqcup C_m
--   $$
--
--   such that each $C_i$ induces a connected subtree of $T$ and has total weight in $[\ell,3\ell]$. Moreover, the quotient graph obtained by contracting each $C_i$ (vertices $1,\dots,m$, with $i\sim j$ when some edge of $T$ joins $C_i$ and $C_j$) is a tree.
--
--   Applied to the weights "node owns an edge" of Lemma 5.3, the clusters become the pieces of the decomposition of Proposition 5.1.
--
--   Differences from the source:
--   - encoding: vertex weights in {0, 1} → w : W → ℕ with w x ≤ 1; reason: same weight functions
--   - encoding: a partition V(T) = C1 ⊔ ⋯ ⊔ Cm into parts inducing connected subtrees; the quotient graph after contracting each Ci → C : Fin m → Finset W pairwise disjoint and covering, each (t.induce (C i)).Connected (hence nonempty); SimpleGraph.fromRel on Fin m joining i ≠ j when an edge of t joins C i and C j; reason: the same partitions and the same contracted graph
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Lemma 5.4, §5.2, p.27 (PDF p.29)

import Mathlib

namespace PlantedSubgraphLD

/-- **Lemma 5.4.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §5.2, Lemma 5.4, p.27 (PDF p.29): "Let T be a finite tree of maximum
degree at most 3 whose vertices have weights in {0, 1}, and let its total weight be t. For every
integer ℓ ≥ 1 with t ≥ ℓ, there is a partition V(T) = C1 ⊔ C2 ⊔ · · · ⊔ Cm, such that each Ci
induces a connected subtree of T and has total weight in [ℓ, 3ℓ]. Moreover, after contracting
each Ci, the quotient graph is a tree."

**Formalization Note** The tree is `t` on a finite type `W` (`SimpleGraph.IsTree`), the weights a
function `w : W → ℕ` with values `≤ 1`. The partition is `C : Fin m → Finset W`, pairwise
disjoint and covering; each part induces a connected subgraph (so it is nonempty). The quotient
graph has vertex set `{1, …, m}` and joins `i ≠ j` when some edge of `t` joins `Cᵢ` and
`Cⱼ`. -/
theorem lemma_5_4 {W : Type} [Fintype W] (t : SimpleGraph W) (ht : t.IsTree)
    (hdeg : ∀ x, (t.neighborSet x).ncard ≤ 3) (w : W → ℕ) (hw : ∀ x, w x ≤ 1)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (htot : ℓ ≤ ∑ x, w x) :
    ∃ (m : ℕ) (C : Fin m → Finset W),
      (Pairwise fun i j => Disjoint (C i) (C j)) ∧ (∀ x, ∃ i, x ∈ C i) ∧
      (∀ i, (t.induce (C i : Set W)).Connected) ∧
      (∀ i, ℓ ≤ ∑ x ∈ C i, w x ∧ ∑ x ∈ C i, w x ≤ 3 * ℓ) ∧
      (SimpleGraph.fromRel fun i j : Fin m => ∃ x ∈ C i, ∃ y ∈ C j, t.Adj x y).IsTree := by sorry

end PlantedSubgraphLD
