-- Prove2me | Theorems.Thm_SemiStreamReach_Main_lemma_19
-- name    : SemiStreamReach.Main.lemma_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:52:28.103393+00:00
-- url     : https://prove2.me/theorems/68c7c318-76b1-455c-b19d-5256ab4786bc
-- title:
--   Lemma 19 — skeletons find all new vertices: $U_F\subseteq U_B$, and $U_F=U_B$ if $|U_F|<\tau$
-- statement:
--   Let $G_0=G\cup H_0$ be a weighted directed graph with positive weights on a finite vertex set, $B$ a block, $\alpha>0$, $r\in\mathbb N$, and let $S$ be the set of vertices settled before round $r$, with integer estimates $d(u)$. Suppose that $\mathrm{Known}_B=B\cap S$, stored with the block distances $d_B(u)=\min_{y\in B\cap S}\big(d(y)+\mathrm{dist}_B(y,u)/\alpha\big)$. Let $\tau\ge1$ be an integer and $F$ a $\tau$-skeleton of $G_0[B]$ without the edges into $\mathrm{Known}_B$, and let $U_F=\{v\in B\setminus \mathrm{Known}_B: d_F(v)\le r\}$ and $U_B$ be as defined in BoundedSSSP. Then
--   $$U_F\subseteq U_B,\qquad\text{and}\qquad |U_F|<\tau\ \Longrightarrow\ U_F=U_B.$$
--
--   A search of a block therefore reports only newly settled vertices, and all of them once it finds fewer than $\tau$; this is what lets SearchBlock double $\tau$ until it succeeds.
--
--   Differences from the source:
--   - generalization: Known_B and d(u) are those of Algorithm 1 at the start of round r (invariants (I1)-(I4)), for a block of Problem 13 with |B| ≤ x → any finite block B, any set S of settled vertices with any natural estimates d, any r and τ ≥ 1, and any τ-skeleton F; reason: the proof uses only the definitions of d_B, d_F, U_B, U_F and of a τ-skeleton; the Lean statement specializes to the algorithm's state
--   - encoding: G ∪ H0 with positive weights; d_B, d_F real or ∞ → one graph G0 with PositiveWeights; values in ℝ≥0∞; Known_B = B ∩ S stored with d_B (blockDist); reason: Lean convention; same instances
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 19 (PDF 21), Lemma 19

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_BatchedDijkstra

open scoped ENNReal
open Classical

namespace SemiStreamReach.Main

/-- Lemma 19 (Skeletons find all new vertices), p. 19 (PDF 21). `G0 = G ∪ H0` has positive
weights (Problem 13), `B` is a block, `S` the set of vertices settled before round `r` with integer
estimates `d`, `Known_B = B ∩ S` stored with the block distances `d_B`, and `F` is a `τ`-skeleton of
`G0[B]` without the edges into `Known_B`. Then `U_F ⊆ U_B`, and `U_F = U_B` if `|U_F| < τ`. -/
theorem lemma_19 {V : Type*} [Fintype V] (G0 F : WGraph V) (B S : Finset V) (d : V → ℕ)
    (α : ℝ) (r τ : ℕ) (hG : PositiveWeights G0) (hα : 0 < α) (hτ : 1 ≤ τ)
    (hF : IsSkeleton G0 B (B ∩ S) τ F) :
    setUF G0 F B S d α r ⊆ setUB G0 B S d α r ∧
      ((setUF G0 F B S d α r).card < τ → setUF G0 F B S d α r = setUB G0 B S d α r) := by sorry

end SemiStreamReach.Main
