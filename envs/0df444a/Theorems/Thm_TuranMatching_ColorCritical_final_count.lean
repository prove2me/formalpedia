-- Prove2me | Theorems.Thm_TuranMatching_ColorCritical_final_count
-- name    : TuranMatching.ColorCritical.final_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:48.585058+00:00
-- url     : https://prove2.me/theorems/53643077-f7ef-4881-aca7-61e9d878a856
-- title:
--   Proof of Prop. 3.1, pp. 5–6 — with |X| = s, V − X independent and at most t(s+m,k) edges inside X ∪ Z, G has at most g(n,k,s) edges
-- statement:
--   Let $k\ge 2$, write $m=\lfloor s/(k-1)\rfloor$, and let $G$ be a graph on $n$ vertices. Suppose that $X$ and $Z$ are disjoint vertex sets with $|X|=s$ and $|Z|=m$ such that
--
--   1. $V-X$ is an independent set in $G$, and
--   2. the subgraph of $G$ induced on $X\cup Z$ has at most $t(s+m,k)$ edges.
--
--   Then
--   $$|E(G)|\le g(n,k,s).$$
--
--   This is the closing count of the proof of Proposition 3.1: the edges inside $X\cup Z$ are bounded by Simonovits' theorem, every other edge joins one of the $n-s-m$ vertices outside $X\cup Z$ to $X$, and the resulting total $t(s+m,k)+(n-s-m)s$ equals $g(n,k,s)$.
--
--   **Formalization Note** The edges of the induced subgraph on $X\cup Z$ are the edges of $G$ both of whose ends lie in $X\cup Z$ (`G.edgeFinset ∩ (X ∪ Z).sym2`). $\lfloor s/(k-1)\rfloor$ is natural-number division.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, pp. 5–6, proof of Proposition 3.1, fifth paragraph (last sentences of p. 5 and first sentences of p. 6)

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

open Finset SimpleGraph

namespace TuranMatching.ColorCritical

theorem final_count {n k s : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X Z : Finset (Fin n)) (hX : #X = s) (hXZ : Disjoint X Z) (hZ : #Z = s / (k - 1))
    (hind : ∀ y z : Fin n, y ∉ X → z ∉ X → ¬ G.Adj y z)
    (hT : #(G.edgeFinset ∩ (X ∪ Z).sym2) ≤ TuranMatching.Clique.turanNum (s + s / (k - 1)) k) :
    #G.edgeFinset ≤ TuranMatching.Clique.gNum n k s := by sorry

end TuranMatching.ColorCritical
