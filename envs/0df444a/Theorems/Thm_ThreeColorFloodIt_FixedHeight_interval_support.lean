-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_interval_support
-- name    : ThreeColorFloodIt.FixedHeight.interval_support
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:15.13002+00:00
-- url     : https://prove2.me/theorems/6217b60b-d47a-4b81-a82f-3ad672c4a266
-- title:
--   Lemma 15 — Interval support and no lost component
-- statement:
--   On a complete positive-height grid, let $S$ be a nonempty connected region. Its occupied columns form an interval, and whenever it meets column $B_j$, every component of its processed part reaches that column:
--   $$\operatorname{cc}(G[S\cap V_{\le j}])\text{ all meet }B_j.$$
--   For any partial region $R\subseteq V_{\le j}$ and any later extension $U$, a component of $R$ disjoint from $B_j$ remains exactly the same component in $R\cup U$. In particular it cannot join another processed component. These three conclusions justify support and retirement checks without requiring connected window intersections.
--
--   Differences from the source:
--   - generalization: the three-row setup in Section 4 → all positive heights and widths with full connectivity partitions; reason: Section 5.1 explicitly carries these invariants and arguments to every height; height three is an instance
--   - encoding: finite graphs, vertices, colors and finite rooted trees → Mathlib simple graphs, finite named carriers, a shared rooted-tree model and explicit legal-sequence predicates; reason: the same source instances are represented; unused palette colors and unowned tree nodes remain allowed
--   - generalization: a processed component disjoint from the current column cannot be joined to another component by later columns, during construction → for any set R inside the prefix V≤j and any set U in columns after j, a vertex of R with no path in R to column j has the same reachability in R ∪ U as in R; reason: the source's processed region and later additions are instances; the proof uses only the column separator
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 12 (PDF 13), Lemma 15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_connectivity

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem interval_support (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    (∀ S : Set (Cell k n), ConnectedSet (Grid k n) S →
      (∀ i j l : Fin n, i ≤ j → j ≤ l → (S ∩ Column i).Nonempty →
        (S ∩ Column l).Nonempty → (S ∩ Column j).Nonempty) ∧
      (∀ j : Fin n, (S ∩ Column j).Nonempty → NoLost (S ∩ Prefix j) j)) ∧
    (∀ (j : Fin n) (R U : Set (Cell k n)) (u : Cell k n), R ⊆ Prefix j →
      U ⊆ {v | j < v.2} → u ∈ R →
      (¬ ∃ r : Fin k, Within (Grid k n) R u (r, j)) →
      ∀ v, Within (Grid k n) (R ∪ U) u v ↔ Within (Grid k n) R u v) := by sorry

end ThreeColorFloodIt.FixedHeight
