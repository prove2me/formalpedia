-- Prove2me | Theorems.Thm_SemiStreamReach_Main_lemma_20
-- name    : SemiStreamReach.Main.lemma_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:52:29.024131+00:00
-- url     : https://prove2.me/theorems/ac4bc621-f1ef-4cec-9a76-1eaf97f59709
-- title:
--   Lemma 20 — a successful skeleton search returns exact block distances and the next block distance
-- statement:
--   In the setting of Lemma 19 (positive weights, $\mathrm{Known}_B=B\cap S$ stored with the block distances $d_B$, $F$ a $\tau$-skeleton of $G_0[B]$ without the edges into $\mathrm{Known}_B$), suppose $|U_F|<\tau$. Then
--   $$d_F(v)=d_B(v)\quad\text{for all } v\in U_F,$$
--   and
--   $$\min\{d_F(v): v\in B\setminus(\mathrm{Known}_B\cup U_F)\}\ =\ \min\{d_B(v): v\in B\setminus(\mathrm{Known}_B\cup U_F)\}.$$
--
--   So a successful search stores the correct block distances and returns as $e_B$ the smallest block distance outside the updated $\mathrm{Known}_B$, which schedules the next search of the block.
--
--   **Formalization Note.** Both minima are infima in `ℝ≥0∞`, equal to $\infty$ when $B\setminus(\mathrm{Known}_B\cup U_F)$ is empty.
--
--   Differences from the source:
--   - generalization: Known_B and d(u) are those of Algorithm 1 at the start of round r (invariants (I1)-(I4)), for a block of Problem 13 with |B| ≤ x → any finite block B, any set S of settled vertices with any natural estimates d, any r and τ ≥ 1, and any τ-skeleton F; reason: the proof uses only the definitions of d_B, d_F, U_B, U_F and of a τ-skeleton; the Lean statement specializes to the algorithm's state
--   - encoding: G ∪ H0 with positive weights; d_B, d_F real or ∞ → one graph G0 with PositiveWeights; values in ℝ≥0∞; Known_B = B ∩ S stored with d_B (blockDist); reason: Lean convention; same instances
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 20 (PDF 22), Lemma 20

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_BatchedDijkstra

open scoped ENNReal
open Classical

namespace SemiStreamReach.Main

/-- Lemma 20, p. 20 (PDF 22). In the setting of Lemma 19, if `|U_F| < τ` then
`d_F(v) = d_B(v)` for every `v ∈ U_F`, and the smallest value `d_F(v)` over
`v ∈ B \ (Known_B ∪ U_F)` equals the smallest block distance `d_B(v)` over the same vertices
(both `⊤` when there is no such vertex). -/
theorem lemma_20 {V : Type*} [Fintype V] (G0 F : WGraph V) (B S : Finset V) (d : V → ℕ)
    (α : ℝ) (r τ : ℕ) (hG : PositiveWeights G0) (hα : 0 < α) (hτ : 1 ≤ τ)
    (hF : IsSkeleton G0 B (B ∩ S) τ F) (hcard : (setUF G0 F B S d α r).card < τ) :
    (∀ v ∈ setUF G0 F B S d α r,
        skelDist F (B ∩ S) (blockDist G0 B S d α) α v = blockDist G0 B S d α v) ∧
      (⨅ v ∈ B \ (B ∩ S ∪ setUF G0 F B S d α r),
          skelDist F (B ∩ S) (blockDist G0 B S d α) α v) =
        ⨅ v ∈ B \ (B ∩ S ∪ setUF G0 F B S d α r), blockDist G0 B S d α v := by sorry

end SemiStreamReach.Main
