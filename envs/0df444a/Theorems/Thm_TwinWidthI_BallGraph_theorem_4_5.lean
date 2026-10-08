-- Prove2me | Theorems.Thm_TwinWidthI_BallGraph_theorem_4_5
-- name    : TwinWidthI.BallGraph.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:53.349968+00:00
-- url     : https://prove2.me/theorems/b7d4cca5-f7c2-4d9e-b010-8a892086e3a0
-- title:
--   Theorem 4.5, p. 3:15 — subgraphs of unit $d$-dimensional ball graphs with clique number $k$ have twin-width at most $(3\lceil\sqrt d\rceil)^d k$
-- statement:
--   Let $d,k\ge 0$, let $V$ be a finite set and $c:V\to\mathbb R^d$, and let $G$ be the unit $d$-dimensional ball graph with centres $c$: distinct $u,v\in V$ are adjacent iff the closed unit balls around $c(u)$ and $c(v)$ meet, i.e. $\|c(u)-c(v)\|_2\le 2$. Suppose $G$ has clique number at most $k$. Then every subgraph $H$ of $G$ (on a vertex set $S\subseteq V$, with every edge of $H$ an edge of $G$) satisfies
--   $$\operatorname{tww}(H)\le d':=(3\lceil\sqrt d\,\rceil)^d\,k .$$
--
--   Unit disk graphs without a bound on the clique number have unbounded twin-width (p. 3:16), so the clique-number bound is what makes the class tractable; with the paper's main theorem this gives FPT first-order model checking on these graphs, given a contraction sequence.
--
--   **Formalization Note.** "Clique number $k$" is encoded as "no clique of size $k+1$" (`CliqueFree (k+1)`), i.e. clique number at most $k$; this is the same theorem since the bound is monotone in $k$. "Subgraph" allows deleting vertices (the finite set $S$) and edges ($H\le G[S]$). $\lceil\sqrt d\,\rceil$ is the natural-number ceiling of the real square root, so $d'$ is a natural number. Twin-width is the partition-form predicate `TwinWidthLE` of the Setting. The second sentence of the theorem (a $d'$-contraction sequence can be found in polynomial time from a geometric representation) is about running time and is not formalized.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:15, Theorem 4.5 (first sentence); proof p. 3:16

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting

namespace TwinWidthI.BallGraph

/-- Theorem 4.5, p. 3:15: every subgraph `H` of a unit d-dimensional ball graph `G` with clique
number (at most) `k` has twin-width at most `(3⌈√d⌉)^d k`. -/
theorem theorem_4_5 (d k : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → EuclideanSpace ℝ (Fin d)) (hK : (ballGraph c).CliqueFree (k + 1))
    (S : Finset V) (H : SimpleGraph S) (hH : H ≤ (ballGraph c).induce (S : Set V)) :
    TwinWidthI.BoolWidth.TwinWidthLE H ((3 * ⌈Real.sqrt d⌉₊) ^ d * k) := by sorry

end TwinWidthI.BallGraph
