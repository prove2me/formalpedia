-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_Supplement_theorem_4_1
-- name    : SuperRamanujan227.Main.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:47:08.054224+00:00
-- url     : https://prove2.me/theorems/cb6db87c-7a83-4164-8913-f512422e8893
-- title:
--   Theorem 4.1 — Sharper constructive bipartite bound
-- statement:
--   There is a single deterministic algorithm with constants $C>0$ and $k\in\mathbb N$ which, for every even integer $n$ and every integer $3\le d\le n/2$, outputs a $d$-regular bipartite multigraph $G$ on $n$ vertices in at most $C(n+1)^k$ machine steps. With $\lambda$ denoting the two-sided nontrivial adjacency parameter, it satisfies the full pair of inequalities
--
--   $$\lambda(G)\le2\sqrt{d-1}\sqrt{1-\frac{2(d-2)}{nd-4}}<2\sqrt{d-1}-\frac{\sqrt d}{2n}.$$
--
--   Both the sharp square-root bound and its strict comparison are part of the conclusion. This companion sharpens Theorem 1.2 while retaining its uniform algorithmic guarantee. The runtime polynomial is existential, as in the paper.
--
--   Differences from the source:
--   - encoding: an algorithm running in time poly(n) → one finite binary multi-stack machine with uniform bound C(n+1)^k; reason: fixed finite machine instructions and framed binary encodings preserve polynomial bit time; the constants precede all inputs
--   - encoding: the largest absolute nontrivial eigenvalue → maximum after deleting one top eigenvalue and, for a bipartite graph, one bottom eigenvalue, with multiplicity; reason: this removes the canonical trivial directions and retains extra copies in disconnected graphs
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), p. 13, Theorem 4.1

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Supplement_Spectral
import Definitions.Def_SuperRamanujan227_Main_Supplement_Computation

namespace SuperRamanujan227.Main.Supplement

/-- Theorem 4.1, p.13: both the sharp bound and its strict comparison are retained. -/
theorem theorem_4_1 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C k : ℕ), 0 < C ∧
      ∀ (n d : ℕ), Even n → 3 ≤ d → d ≤ n / 2 →
        ∃ G : Multigraph n, G.IsRegular d ∧ MatrixBipartite G.adj ∧
          spectralRadius G ≤ 2 * Real.sqrt ((d : ℝ) - 1) *
            Real.sqrt (1 - 2 * ((d : ℝ) - 2) / ((n : ℝ) * (d : ℝ) - 4)) ∧
          2 * Real.sqrt ((d : ℝ) - 1) *
            Real.sqrt (1 - 2 * ((d : ℝ) - 2) / ((n : ℝ) * (d : ℝ) - 4)) <
            2 * Real.sqrt ((d : ℝ) - 1) - Real.sqrt d / (2 * (n : ℝ)) ∧
          Runs M (graphInput n d) (graphOutput G) (C * (n + 1)^k) := by sorry

end SuperRamanujan227.Main.Supplement
