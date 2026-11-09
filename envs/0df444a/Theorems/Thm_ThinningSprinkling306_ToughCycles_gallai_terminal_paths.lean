-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_gallai_terminal_paths
-- name    : ThinningSprinkling306.ToughCycles.gallai_terminal_paths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:58.718199+00:00
-- url     : https://prove2.me/theorems/ad6776d4-2454-4cd3-9eda-4d67bb46f3ac
-- title:
--   Proposition 5.1 — Gallai terminal-path packing or transversal
-- statement:
--   Let $G$ be any finite simple graph, let $A$ be a vertex subset, and let $k\ge0$ be an integer. An $A$-path is a simple positive-length path with both endpoints in $A$, with no restriction on internal terminals. Then
--   $$
--   \text{$G$ has $k$ vertex-disjoint $A$-paths}
--   \quad\text{or}\quad
--   \exists Z\subseteq V(G),\ |Z|\le2k-2,\ \text{$G-Z$ has no $A$-path}.
--   $$
--   Disjointness includes endpoints, and surviving terminals are $A\setminus Z$. At $k=0$ the empty packing satisfies the first alternative. This classical result supplies the path-packing or small-transversal dichotomy used in Lemma 5.2.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - encoding: the integer upper bound 2k−2 → integer subtraction in the transversal bound, including k=0; reason: the bound is not truncated; the empty packing supplies the k=0 case
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 11, Proposition 5.1 ([23]) (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Paths

namespace ThinningSprinkling306.ToughCycles

/-- Proposition 5.1, printed p. 11 (PDF p. 13), Gallai's A-path theorem. -/
theorem gallai_terminal_paths {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (k : ℕ) :
    HasTerminalPacking G A k ∨
      ∃ Z : Finset (Fin n), (Z.card : ℤ) ≤ 2 * (k : ℤ) - 2 ∧
        ∀ P : Path G, P.vertices ⊆ Finset.univ \ Z → ¬ TerminalPath A P := by sorry

end ThinningSprinkling306.ToughCycles
