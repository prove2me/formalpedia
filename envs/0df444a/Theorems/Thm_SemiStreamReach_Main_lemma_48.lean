-- Prove2me | Theorems.Thm_SemiStreamReach_Main_lemma_48
-- name    : SemiStreamReach.Main.lemma_48
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:52:09.782359+00:00
-- url     : https://prove2.me/theorems/c3ef7c82-367f-496e-b023-514241274c29
-- title:
--   Lemma 48 — PositiveOracle turns $(1+\varepsilon/3)$-approximate distances in $A^+$ into $(1+\varepsilon)$-approximate distances in $A$
-- statement:
--   Let $A$ be a directed graph with $n_A$ vertices and nonnegative integer weights $w_A$, let $s_A$ be a vertex of $A$, and let $0<\varepsilon\le1$. Put $\theta=\lceil 3n_A/\varepsilon\rceil$ and let $A^+$ be $A$ with weights $\theta w_A+1$. If $\hat d^+$ is a vector of $(1+\varepsilon/3)$-approximate distances from $s_A$ in $A^+$, then the vector returned by PositiveOracle,
--   $$\hat d(v)=\begin{cases}0,&\hat d^+(v)<\theta,\\ \hat d^+(v)/\theta,&\text{otherwise,}\end{cases}$$
--   is a vector of $(1+\varepsilon)$-approximate distances from $s_A$ in $A$.
--
--   It lets an approximate algorithm that needs positive weights answer the oracle calls of the exact-from-approximate reduction, whose graphs may have zero weights.
--
--   Differences from the source:
--   - encoding: A with n_A vertices and nonnegative integer weights; the approximate algorithm's estimates; ∞ for unreachable vertices → vertex set Fin n_A, edge set E with natural weights (ofEdges); d̂⁺ any vector in ℝ≥0∞ meeting the (1 + ε/3) guarantee; reason: Lean convention; the lemma concerns the returned estimates, whatever algorithm produced them
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 57 (PDF 59), Lemma 48

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_PositiveOracle

open scoped ENNReal

namespace SemiStreamReach.Main

/-- Lemma 48, p. 57 (PDF 59). Let `A` be a directed graph on `n_A` vertices with edge set `E` and
nonnegative integer weights `w_A`, `s_A` a vertex, `0 < ε ≤ 1`, `θ = ⌈3n_A/ε⌉`, and `A+` the graph
with weights `θ w_A + 1`. If `d̂+` is a vector of `(1 + ε/3)`-approximate distances from `s_A` in
`A+`, then PositiveOracle's answer (`0` where `d̂+ < θ`, else `d̂+/θ`) is a vector of
`(1 + ε)`-approximate distances from `s_A` in `A`. -/
theorem lemma_48 {nA : ℕ} (E : Finset (Fin nA × Fin nA)) (wA : Fin nA × Fin nA → ℕ)
    (sA : Fin nA) (ε : ℝ) (dplus : Fin nA → ℝ≥0∞) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hd : IsApproxDist (ofEdges E (plusWeights (oracleTheta nA ε) wA)) sA (ε / 3) dplus) :
    IsApproxDist (ofEdges E wA) sA ε (oracleAnswer (oracleTheta nA ε) dplus) := by sorry

end SemiStreamReach.Main
