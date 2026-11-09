-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_short_or_escape_paths
-- name    : ThinningSprinkling306.ToughCycles.short_or_escape_paths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:17.154241+00:00
-- url     : https://prove2.me/theorems/7087e1d3-bf65-471b-b659-4b3c3de8b50b
-- title:
--   Lemma 4.3 — short connecting or escaping paths
-- statement:
--   Let $G$ be $t$-tough, and let $C_1,\ldots,C_k$ be disjoint nonempty vertex sets, where $k\ge2$, with no graph edge between distinct sets. Write $D=\bigcup_j C_j$ and let $N_G(D)$ be its external neighborhood. Then there is a finite family of paths, intersecting only on $D$, of cardinality $r$ with
--   $$
--   r\ge\frac{kt}{2}.
--   $$
--   Each path either has length at most three and joins two distinct $C_j$, or has length two with one endpoint in a $C_j$ and the other outside $D\cup N_G(D)$. Endpoints in $D$ may be shared.
--
--   The result supplies the two exact types of path opportunities needed by the sampling statements, with the real lower bound retained.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - encoding: at least a displayed real number of paths → a natural family size r satisfying the same real lower bound; reason: this is the ceiling interpretation and preserves the exact displayed constant
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 9, Lemma 4.3 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Paths

namespace ThinningSprinkling306.ToughCycles

/-- Lemma 4.3, printed p. 9 (PDF p. 11). -/
theorem short_or_escape_paths {n k : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ)
    (C : Fin k → Finset (Fin n)) (hk : 2 ≤ k) (hG : Tough G t)
    (hne : ∀ i, (C i).Nonempty)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hnoedges : ∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, ¬ G.Adj u v) :
    ∃ r : ℕ, ∃ P : Fin r → Path G,
      (k : ℝ) * t / 2 ≤ (r : ℝ) ∧ DisjointOutside (unionParts C) P ∧
      ∀ i, ((P i).walk.length ≤ 3 ∧ JoinsParts C (P i)) ∨
        ((P i).walk.length = 2 ∧ (∃ j, (P i).first ∈ C j) ∧
          (P i).last ∉ unionParts C ∪ externalNeighbors G (unionParts C)) := by sorry

end ThinningSprinkling306.ToughCycles
