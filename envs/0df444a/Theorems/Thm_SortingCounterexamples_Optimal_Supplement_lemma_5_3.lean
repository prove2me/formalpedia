-- Prove2me | Theorems.Thm_SortingCounterexamples_Optimal_Supplement_lemma_5_3
-- name    : SortingCounterexamples.Optimal.Supplement.lemma_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:37:36.125314+00:00
-- url     : https://prove2.me/theorems/ea82f1f7-1220-4d60-8b8a-9b80b11c2d13
-- title:
--   Lemma 5.3 — every comparison of a linear extension of $G_t$ has weight at least $1/(d+1)$
-- statement:
--   Let $v_1,\dots,v_n\in\mathbb R^d$ and let $H$ be a nonempty finite $d$-dimensional geometric class of rankings with this representation. For any transcript, let $p(i,j)$ be the probability that a ranking drawn from $H$ with the normalized weighted-majority weights places $i$ before $j$, and let $G$ be the strong-majority graph with an edge $i\to j$ for distinct $i,j$ whenever $p(i,j)>1-\frac1{d+1}$. If a ranking $\hat\pi$ is a linear extension of $G$ (it places $i$ before $j$ for every edge $i\to j$) and $\hat\pi$ places $i$ before $j$, then
--   $$p(i,j)\ \ge\ \frac1{d+1}.$$
--
--   This is the progress guarantee of the upper bound: whichever pair the oracle returns, the rankings that agree with the query on it carry at least a $1/(d+1)$ fraction of the weight, so the total weight drops by a factor $1-\frac1{2(d+1)}$ (eq. (11)).
--
--   Differences from the source:
--   - generalization: π̂_t, the linear extension of G_t queried by the learner at time t → every linear extension π̂ of G for the weights after any transcript; reason: the learner's query is one such extension of the graph of its own transcript, so the source's statement is a special case
--   - encoding: P_t is a probability distribution on H → H nonempty; reason: normalization by Q_t is defined only for nonempty H; for empty H Lean's division by zero would give p = 0
-- source:
--   Noga Alon, Shay Moran, Shlomo Moran, STOC 2027 submission #549 (October 2026), printed p. 24 / PDF p. 25, Lemma 5.3; graph G_t from eq. (8), printed p. 23 / PDF p. 24; setting printed p. 22 / PDF p. 23

import Mathlib
import Definitions.Def_SortingCounterexamples_Optimal_Protocol
import Definitions.Def_SortingCounterexamples_Optimal_Supplement_Geometric

namespace SortingCounterexamples.Optimal.Supplement

open SortingCounterexamples.Optimal

/-- Lemma 5.3: for a nonempty `d`-dimensional geometric class `H` and the weights after any
transcript `h`, every linear extension `π̂` of the strong-majority graph `G_t` orients only
pairs with support at least `1/(d+1)`: if `π̂` places `i` before `j`, then
`p_t(i, j) ≥ 1/(d+1)`. -/
theorem lemma_5_3 {n d : ℕ} (v : Fin n → Fin d → ℝ) (H : Finset (Ranking n))
    (hH : IsGeometricClass v H) (hne : H.Nonempty) (h : Transcript n) (πhat : Ranking n)
    (hext : IsLinearExtension πhat (MajorityEdge d H h)) :
    ∀ i j : Fin n, πhat.Before i j → 1 / ((d : ℝ) + 1) ≤ pairProb H h i j := by sorry

end SortingCounterexamples.Optimal.Supplement
