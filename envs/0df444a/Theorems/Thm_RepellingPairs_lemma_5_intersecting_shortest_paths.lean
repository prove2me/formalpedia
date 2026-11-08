-- Prove2me | Theorems.Thm_RepellingPairs_lemma_5_intersecting_shortest_paths
-- name    : RepellingPairs.lemma_5_intersecting_shortest_paths
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:01:53.05862+00:00
-- url     : https://prove2.me/theorems/d28dac19-5dc9-4028-842d-f23f8036f06e
-- title:
--   Lemma 5 — intersecting shortest paths do not repel
-- statement:
--   Let $P$ be an $a$-$b$ shortest path and $Q$ a $c$-$d$ shortest path in a finite multigraph with nonnegative edge lengths. If $P$ and $Q$ share a vertex, then
--
--   $$
--   \mathrm{dist}_G(a,b)+\mathrm{dist}_G(c,d)\ge\mathrm{dist}_G(a,c)+\mathrm{dist}_G(b,d),
--   $$
--   $$
--   \mathrm{dist}_G(a,b)+\mathrm{dist}_G(c,d)\ge\mathrm{dist}_G(a,d)+\mathrm{dist}_G(b,c).
--   $$
--
--   This gives the forward direction of Theorem 1: if lengths realize the structure, the paths of a repelling pair cannot meet.
--
--   Differences from the source:
--   - encoding: dist_G is a real number → dist_G takes values in [0, ∞], with ∞ when no path exists; reason: the page does not name a value for disconnected vertices; here all four sums are between connected vertices, because P and Q meet
--   - reading: a weighted graph → a finite multigraph with nonnegative edge lengths; reason: §2, p.5: "All graphs are finite and may have nonnegative edge lengths", with parallel edges as in the proof of Lemma 33
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Lemma 5, p.6

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_PathLength

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- **Lemma 5.** If an `a`-`b` shortest path and a `c`-`d` shortest path intersect, then
`dist(a, b) + dist(c, d) ≥ dist(a, c) + dist(b, d)` and `dist(a, b) + dist(c, d) ≥ dist(a, d) + dist(b, c)`.
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), Lemma 5, p.6.

**Formalization Note.** Nonnegative edge lengths (§2, p.5); no embedding. Distances are in `ℝ≥0∞`. -/
theorem lemma_5_intersecting_shortest_paths {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (G : Multigraph V E) (ℓ : E → ℝ) (hℓ : ∀ e, 0 ≤ ℓ e) {a b c d : V}
    (P : G.Path a b) (Q : G.Path c d) (hP : P.1.IsShortest ℓ) (hQ : Q.1.IsShortest ℓ)
    (hint : ¬ P.1.VertexDisjoint Q.1) :
    G.distG ℓ a c + G.distG ℓ b d ≤ G.distG ℓ a b + G.distG ℓ c d ∧
      G.distG ℓ a d + G.distG ℓ b c ≤ G.distG ℓ a b + G.distG ℓ c d := by sorry

end RepellingPairs
