-- Prove2me | Theorems.Thm_ShortBroadcastDom_lemma_4_1_orientation
-- name    : ShortBroadcastDom.lemma_4_1_orientation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:36.062566+00:00
-- url     : https://prove2.me/theorems/48378c1a-8fc4-467e-b37c-e69a501c1b16
-- title:
--   Lemma 4.1 — subgraph density $p$ gives an orientation of maximum outdegree $p$
-- statement:
--   Let $p\ge 1$ be an integer and $G$ a finite graph such that every subgraph $H$ of $G$ satisfies $|E(H)|\le p\,|V(H)|$. Then $G$ has an **orientation** of maximum outdegree at most $p$: each edge $uv$ can be directed as $u\to v$ or $v\to u$ so that every vertex has at most $p$ outgoing edges.
--
--   This is the relevant special case of Hakimi's orientation theorem; the orientation is used only in proofs (Lemma 6.10), never computed by an algorithm.
--
--   **Formalization Note** An orientation is a relation $o$ with $o(u,v)\Rightarrow uv\in E(G)$ and, for every edge, exactly one of $o(u,v)$, $o(v,u)$.
--
--   Differences from the source:
--   - encoding: every subgraph H satisfies |E(H)| ≤ p|V(H)| → every induced subgraph (SubgraphDensityLE p G); reason: an arbitrary subgraph has at most as many edges as the induced subgraph on its vertex set
--   - encoding: an orientation of maximum outdegree at most p → a relation o ⊆ E(G) choosing exactly one direction per edge, with |{w : o v w}| ≤ p; reason: the same object
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §4, p.15 (PDF p.18), Lemma 4.1

import Mathlib
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE

namespace ShortBroadcastDom

/-- **Lemma 4.1 (bounded-outdegree orientation).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §4, p.15 (PDF 18): "If every subgraph H
of G satisfies |E(H)| ≤ p|V(H)| for an integer p ≥ 1, then G has an orientation of maximum
outdegree at most p."

**Formalization Note** An orientation is a relation `o` with `o u v → G.Adj u v` and, for every
edge `uv`, exactly one of `o u v`, `o v u`; the outdegree of `v` is the number of `w` with `o v w`.
"Every subgraph" is `SubgraphDensityLE p G` (induced subgraphs, which is equivalent). -/
theorem lemma_4_1_orientation {V : Type} [Fintype V] (G : SimpleGraph V) (p : ℕ) (hp : 1 ≤ p)
    (hG : SubgraphDensityLE (p : ℝ) G) :
    ∃ o : V → V → Prop, (∀ u v, o u v → G.Adj u v) ∧ (∀ u v, G.Adj u v → (o u v ↔ ¬ o v u)) ∧
      ∀ v, {w | o v w}.ncard ≤ p := by sorry

end ShortBroadcastDom
