-- Prove2me | Theorems.Thm_SteinerNav_construction_edge_count
-- name    : SteinerNav.construction_edge_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:35.004199+00:00
-- url     : https://prove2.me/theorems/b1ab471b-9861-412c-92c0-12ae66487f6d
-- title:
--   Proof of Theorem 3, p.9 — edge types 1 and 2 contribute at most $n|R|+n(m+|S|)\le 2nma+nm=O(nma)$
-- statement:
--   Let $P\subset\mathbb R^d$ have $n$ points, $Q\subseteq P$ landmarks, $S$ sampled locations and $R=S\setminus P$, and let $T$ be the number of type-3 edges. Then
--
--   1. the graph of Theorem 3's construction has at most $n|R|+n(|Q|+|S|)+T$ edges;
--   2. if $|Q|=m$ and $|S|\le ma$, edge types 1 and 2 contribute at most
--   $$n|R|+n(m+|S|)\ \le\ 2nma+nm,$$
--   and $2nma+nm\le 3nma=O(nma)$ when $a\ge1$.
--
--   Together with the count of type-3 edges this gives the edge bound of Theorem 3.
--
--   Differences from the source:
--   - encoding: "Edge types 1 and 2 contribute at most n|R| + n(m + |S|)" → clause 1 bounds the whole edge set by that sum plus the type-3 count T; reason: the edge set is the union of the three types, so this is the same count stated for the graph the page builds.
--   - encoding: "= O(nma)" → ≤ 3nma for a ≥ 1; reason: a = KL ≥ 1 on the page, and 3 is the explicit constant.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 3, p.9 (display after the navigability paragraph); |S| ≤ ma, p.8

import Mathlib
import Definitions.Def_SteinerNav_constructionEdges

namespace SteinerNav

/-- Proof of Theorem 3, edge count: the graph has at most `n|R| + n(|Q| + |S|) + T` edges, with `T` the
number of type-3 pairs, and when `|Q| = m` and `|S| ≤ ma`, edge types 1 and 2 contribute at most
`2nma + nm = O(nma)`, namely at most `3nma` once `a ≥ 1` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 3, p.9). -/
theorem construction_edge_count {d : ℕ} (P Q S : Finset (Pt d)) :
    (constructionEdges P Q S).card ≤
        P.card * (S \ P).card + P.card * (Q.card + S.card) + (type3Edges P Q).card ∧
      ∀ m a : ℕ, Q.card = m → S.card ≤ m * a →
        P.card * (S \ P).card + P.card * (m + S.card) ≤ 2 * P.card * m * a + P.card * m ∧
          (1 ≤ a → 2 * P.card * m * a + P.card * m ≤ 3 * (P.card * m * a)) := by sorry

end SteinerNav
