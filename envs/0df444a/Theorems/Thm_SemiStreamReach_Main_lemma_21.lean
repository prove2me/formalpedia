-- Prove2me | Theorems.Thm_SemiStreamReach_Main_lemma_21
-- name    : SemiStreamReach.Main.lemma_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:52:29.371051+00:00
-- url     : https://prove2.me/theorems/a983b779-2bda-4555-9fca-4d9efb1886fa
-- title:
--   Lemma 21 — BatchedDijkstra (Algorithm 1) solves BoundedSSSP
-- statement:
--   Let $G_0=G\cup H_0$ be a weighted directed graph with positive weights on a finite vertex set $V$, $(B_i)_{i\in\iota}$ a finite family of blocks, $H=H_0\cup\bigcup_i TC_w(G_0[B_i])$, $\alpha>0$, $s\in V$ and $R\in\mathbb N$. Run BatchedDijkstra$(s,R)$ (Algorithm 1) with any choice of the $\tau$-skeletons built by its searches, and let $d$ be the returned estimates. Then for each vertex $v$,
--   $$\mathrm{dist}_{G_\alpha\cup H_\alpha}(s,v)\le R\ \Longrightarrow\ d(v)=\mathrm{dist}_{G_\alpha\cup H_\alpha}(s,v),\qquad \mathrm{dist}_{G_\alpha\cup H_\alpha}(s,v)>R\ \Longrightarrow\ d(v)>R.$$
--
--   This is the correctness half of Theorem 14: the batched variant of Dijkstra's algorithm on $G_\alpha\cup H_\alpha$ never relaxes the (unstored) block-closure edges, and still settles exactly the vertices at distance $r$ in round $r$.
--
--   Differences from the source:
--   - generalization: an instance of Problem 13: |B| ≤ x for all blocks and |H0| + Σ|B| = Õ(n) → any finite family of blocks, any G0 = G ∪ H0 with positive weights; reason: the size bounds only enter the resource analysis (Theorem 14), not correctness; the Lean statement specializes to Problem 13
--   - encoding: Algorithm 1 with its skeletons, executed sequentially → batchedDijkstra with an arbitrary skeleton-choice function sk (constrained by IsSkeleton for every round, block, Known_B and τ), searches of one round applied together, values in ℝ≥0∞, a search that finds no τ returns nothing; reason: every run of the algorithm is one of these; searches of distinct blocks read disjoint data, and the fallback never occurs by the paper's analysis
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 20 (PDF 22), Lemma 21

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_BatchedDijkstra

open scoped ENNReal

namespace SemiStreamReach.Main

/-- Lemma 21, p. 20 (PDF 22). For every instance of BoundedSSSP (Problem 13: `G0 = G ∪ H0` with
positive weights, blocks `Bk i`, `α > 0`, a source `s`, a radius `R`) and every choice of the
`τ`-skeletons used by the searches, BatchedDijkstra (Algorithm 1) returns
`d(v) = dist_{G_α ∪ H_α}(s, v)` if this distance is at most `R`, and `d(v) > R` otherwise. -/
theorem lemma_21 {V ι : Type*} [Fintype V] [Fintype ι] (G0 : WGraph V) (Bk : ι → Finset V)
    (α : ℝ) (s : V) (R : ℕ) (sk : ℕ → ι → Finset V → ℕ → WGraph V)
    (hG : PositiveWeights G0) (hα : 0 < α)
    (hsk : ∀ r i K τ, IsSkeleton G0 (Bk i) K τ (sk r i K τ)) :
    ∀ v : V,
      (dist (roundedUnion G0 Bk α) s v ≤ (R : ℝ≥0∞) →
          batchedDijkstra G0 Bk α sk s R v = dist (roundedUnion G0 Bk α) s v) ∧
        ((R : ℝ≥0∞) < dist (roundedUnion G0 Bk α) s v →
          (R : ℝ≥0∞) < batchedDijkstra G0 Bk α sk s R v) := by sorry

end SemiStreamReach.Main
