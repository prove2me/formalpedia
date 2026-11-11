-- Prove2me | Theorems.Thm_RankingBeats_General_theorem_1_1
-- name    : RankingBeats.General.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:27:27.145315+00:00
-- url     : https://prove2.me/theorems/fb838655-04b9-40af-8227-4727d3591f17
-- title:
--   Theorem 1.1 — Ranking matches at least 0.635 · ν(G) edges in expectation on every finite simple graph
-- statement:
--   Let $G=(V,E)$ be any finite simple graph — not necessarily bipartite, with no condition on degrees, odd girth, connectivity or perfect matchings — and let $\nu(G)=|\mathrm{OPT}|$ be the maximum size of a matching of $G$. Draw ranks $x_v$, $v\in V$, independently and uniformly from $[0,1)$, and let $R(\vec x)$ be the matching output by Ranking (Algorithm 1): process the vertices in increasing order of rank, and match each still-available vertex that has an available neighbour to its available neighbour of smallest rank. Then
--   $$\mathbb E_{\vec x}\big[|R(\vec x)|\big]\ \ge\ 0.635\cdot\nu(G).$$
--   That is, Ranking achieves an approximation ratio of at least $0.635$ on general graphs, above the $1-1/e\approx0.632$ barrier.
--
--   Differences from the source:
--   - encoding: 'Ranking achieves an approximation ratio of at least 0.635', α = E_x[|R(x)|] / |OPT| → 0.635 · ν(G) ≤ E_x[|R(x)|] with ν(G) = StochMatchPoly.mu G.edgeFinset; reason: the form the paper uses (p. 78); it avoids division and covers ν(G) = 0
--   - encoding: Ranking on rank vectors with distinct ranks (ties have probability zero) → ranking is defined on every x : V → ℝ, with ties broken by a fixed [LinearOrder V]; the vertex type carries such an order; reason: every finite type has a linear order, and the tie-break changes R(x) only on a null set, so the expectation is the paper's
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 4, Theorem 1.1 (restated and proved pp. 71–72)

import Mathlib
import Definitions.Def_StochMatchPoly_mu
import Definitions.Def_RankingBeats_General_Ranking

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Theorem 1.1** (p. 4; restated and proved pp. 71–72). Ranking achieves an approximation ratio
of at least `0.635` on every finite simple graph: with i.i.d. Uniform`[0, 1)` ranks,
`E_x[|R(x)|] ≥ 0.635 · ν(G)`, where `ν(G) = |OPT|` is the maximum matching size. -/
theorem theorem_1_1 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    (0.635 : ℝ) * (StochMatchPoly.mu G.edgeFinset : ℝ) ≤ expectedSize G := by sorry

end RankingBeats.General
