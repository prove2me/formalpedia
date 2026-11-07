-- Prove2me | Theorems.Thm_ShortBroadcastDom_lemma_A_1_short_faces
-- name    : ShortBroadcastDom.lemma_A_1_short_faces
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:41.892+00:00
-- url     : https://prove2.me/theorems/b111a2f6-112b-4627-9f4a-543f498395e9
-- title:
--   Lemma A.1 — planar $K$ with $K-A$ of girth $\ge g$: $|E(K)|\le\frac{g}{g-2}|V(K)|+\frac{g-3}{g-2}p$
-- statement:
--   Let $g\ge3$ be an integer, and let $K$ be a finite simple planar graph with an independent set $A\subseteq V(K)$ such that $K-A$ has girth at least $g$. If $p$ edges of $K$ are incident with $A$, then
--
--   $$
--   |E(K)|\le\frac{g}{g-2}\,|V(K)|+\frac{g-3}{g-2}\,p.
--   $$
--
--   In particular (with $A=\emptyset$), every planar graph of girth at least $g$ has density at most $a=g/(g-2)$, and so has each of its subgraphs.
--
--   The first part replaces the minor-density bound in the output count at girths four and six (Lemma A.2); the second places planar graphs of large girth in the non-integer case of §7.3.
--
--   **Formalization Note** Girth at least $g$ is $g\le\mathrm{egirth}$ in $\mathbb N\cup\{\infty\}$ (an acyclic graph has infinite girth).
--
--   Differences from the source:
--   - encoding: K − A has girth at least g → g ≤ egirth of the induced subgraph K.induce Aᶜ; reason: the same graph; acyclic graphs have egirth = ⊤
--   - encoding: each subgraph has a ratio of edges to vertices of at most g/(g − 2) → SubgraphDensityLE (g/(g−2)) K; reason: induced subgraphs suffice
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. A.1, p.61 (PDF p.64), Lemma A.1

import Mathlib
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace ShortBroadcastDom

/-- **Lemma A.1 (short faces at an independent set).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), App. A.1, p.61 (PDF 64): "Let g ≥ 3
and suppose that K is a simple planar graph with an independent set A ⊆ V(K) such that K − A has
girth at least g. If p edges of K are incident with A, then
|E(K)| ≤ (g/(g − 2))|V(K)| + ((g − 3)/(g − 2))p. In particular, with A = ∅, every planar graph of
girth at least g has a ratio of edges to vertices of at most a = g/(g − 2), and so has each of its
subgraphs."

**Formalization Note** Planarity is the published `RobertsonSeymour1986.GM5.IsPlanar`. Girth at
least `g` is `g ≤ egirth` in `ℕ∞` (an acyclic graph has `egirth = ⊤`); `K − A` is the induced
subgraph `K.induce Aᶜ`. `p` counts the edges of `K` with an endpoint in `A`. The "in particular"
clause is the second conjunct. -/
theorem lemma_A_1_short_faces {V : Type} [Fintype V] (g : ℕ) (hg : 3 ≤ g) :
    (∀ (K : SimpleGraph V) (A : Set V), RobertsonSeymour1986.GM5.IsPlanar K →
      (∀ u ∈ A, ∀ v ∈ A, ¬ K.Adj u v) → (g : ℕ∞) ≤ (K.induce Aᶜ).egirth →
        (K.edgeSet.ncard : ℝ) ≤ (g : ℝ) / ((g : ℝ) - 2) * (Fintype.card V : ℝ) +
          ((g : ℝ) - 3) / ((g : ℝ) - 2) *
            (({e | e ∈ K.edgeSet ∧ ∃ v ∈ e, v ∈ A} : Set (Sym2 V)).ncard : ℝ)) ∧
    ∀ K : SimpleGraph V, RobertsonSeymour1986.GM5.IsPlanar K → (g : ℕ∞) ≤ K.egirth →
      SubgraphDensityLE ((g : ℝ) / ((g : ℝ) - 2)) K := by sorry

end ShortBroadcastDom
