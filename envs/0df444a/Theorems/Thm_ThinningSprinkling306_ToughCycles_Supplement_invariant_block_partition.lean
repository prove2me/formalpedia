-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_Supplement_invariant_block_partition
-- name    : ThinningSprinkling306.ToughCycles.Supplement.invariant_block_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:43:57.923204+00:00
-- url     : https://prove2.me/theorems/18a297fb-25e5-4a3f-813e-4778b831dba8
-- title:
--   Lemma 7.1 — invariant blocks with retained degree and edge expansion
-- statement:
--   Let $0<\varepsilon\le1/4$ and let $G$ be a $d$-regular vertex-transitive graph. Connectedness is not assumed. There is a partition into nonempty blocks, permuted by every automorphism of $G$, such that each induced block is regular of degree at least $(1-\varepsilon)d$ and
--   $$
--   e_G(U,B\setminus U)\ge\min\{d|U|/4,\ \varepsilon d^2/10\}
--   \qquad(U\subseteq B,\ 2|U|\le|B|).
--   $$
--   Crossing edges are counted once. The statement includes $U=\varnothing$, $d=0$ and the empty graph. This is the deterministic block structure supporting Theorem 1.3 through the paper's connecting lemmas.
--
--   Differences from the source:
--   - encoding: a block partition and e(U,B minus U) → a finite set of nonempty disjoint blocks invariant under every automorphism, with one-sided incidence edge counts; reason: removes labels without changing any partition or any undirected crossing-edge count
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 13, Lemma 7.1 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_Blocks

open Filter

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Lemma 7.1: no connectedness or positive-degree hypothesis. -/
theorem invariant_block_partition {n : ℕ} (G : SimpleGraph (Fin n))
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (hregular : RegularOn G Finset.univ d) (htrans : DerandSq.IsVertexTransitive G) :
    ∃ B : Finset (Finset (Fin n)), InvariantBlocks G B ∧
      (∀ A ∈ B, ∃ dA : ℕ, (1 - ε) * (d : ℝ) ≤ (dA : ℝ) ∧ RegularOn G A dA) ∧
      ∀ A ∈ B, ∀ U : Finset (Fin n), U ⊆ A → 2 * U.card ≤ A.card →
        min ((d : ℝ) * U.card / 4) (ε * (d : ℝ) ^ 2 / 10) ≤
          (crossingEdges G U (A \ U) : ℝ) := by sorry

end ThinningSprinkling306.ToughCycles.Supplement
