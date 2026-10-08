-- Prove2me | Theorems.Thm_SnarkGen_CycleCover_cycle_cover_four_thirds
-- name    : SnarkGen.CycleCover.cycle_cover_four_thirds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:30.17002+00:00
-- url     : https://prove2.me/theorems/ab705b03-c69b-4764-b52a-36a134257358
-- title:
--   §7, p. 24 — a colourable cubic graph with m edges has a cycle cover of length at most 4m/3
-- statement:
--   Let $G$ be a finite simple cubic graph with $m$ edges that is colourable, i.e. has a proper $3$-edge-colouring. Then $G$ has a cycle cover $\mathcal F$ (a set of cycles of $G$ covering every edge) whose length, the sum of the lengths of its cycles, satisfies
--
--   $$\ell(\mathcal F) \le \frac{4m}{3} .$$
--
--   Equivalently, the shortest cycle cover of a colourable cubic graph has length at most $4m/3$. The bound is the colourable case of the bound in Conjecture 7.4 and lies below the Alon–Tarsi bound $7m/5$ of Conjecture 7.1.
--
--   **Formalization Note** The statement is in $\mathbb N$ with the denominator cleared: $3\,\ell(\mathcal F) \le 4m$, where $m$ is `G.edgeFinset.card`. "The shortest cycle cover has length at most $X$" is stated as "some cycle cover has length at most $X$"; the two agree because a finite graph has finitely many cycle covers, so the minimum is attained. Cycles are genuine cycles (`Walk.IsCycle`), not arbitrary even subgraphs. For the graph with no vertices the empty cover works.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 24, Section 7 (unnumbered consequence of Lemma 7.2 and Proposition 5.3)

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable
import Definitions.Def_SnarkGen_CycleCover_IsCycleCover

namespace SnarkGen.CycleCover

/-- arXiv:1206.6690v3, §7, p. 24: a colourable cubic graph with `m` edges has a cycle cover of
length at most `4m/3` (so its shortest cycle cover has length at most `4m/3`). Stated in `ℕ`
with the denominator multiplied out. -/
theorem cycle_cover_four_thirds {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcubic : G.IsRegularOfDegree 3) (hcol : SnarkGen.EdgeInsertion.Colourable G) :
    ∃ F : Finset (Finset (Sym2 V)), IsCycleCover G F ∧
      3 * coverLength F ≤ 4 * G.edgeFinset.card := by sorry

end SnarkGen.CycleCover
