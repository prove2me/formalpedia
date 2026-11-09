-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_tough_terminal_paths
-- name    : ThinningSprinkling306.ToughCycles.tough_terminal_paths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:01.519774+00:00
-- url     : https://prove2.me/theorems/6c9a8f08-ecb2-45ff-9591-066f63ab550b
-- title:
--   Lemma 5.2 — vertex-disjoint terminal paths in a tough graph
-- statement:
--   Let $G$ be a $t$-tough finite simple graph and let $A\subseteq V(G)$ have at least two vertices. There is a natural number $r$ and a family of $r$ vertex-disjoint $A$-paths such that
--   $$
--   r\ge\frac{\min\{1,t\}|A|}{4}.
--   $$
--   Every path has positive length and both endpoints in $A$, and whole vertex sets are disjoint. The exact constant $1/4$ and the real lower bound are retained. This is the terminal-path packing target used in the reservoir lemma.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - encoding: at least a displayed real number of paths → a natural family size r satisfying the same real lower bound; reason: this is the ceiling interpretation and preserves the exact displayed constant
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 11, Lemma 5.2 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Paths

namespace ThinningSprinkling306.ToughCycles

/-- Lemma 5.2, printed p. 11 (PDF p. 13). -/
theorem tough_terminal_paths {n : ℕ} (G : SimpleGraph (Fin n))
    (t : ℝ) (A : Finset (Fin n)) (hG : Tough G t) (hA : 2 ≤ A.card) :
    ∃ r : ℕ, min 1 t * (A.card : ℝ) / 4 ≤ (r : ℝ) ∧
      HasTerminalPacking G A r := by sorry

end ThinningSprinkling306.ToughCycles
