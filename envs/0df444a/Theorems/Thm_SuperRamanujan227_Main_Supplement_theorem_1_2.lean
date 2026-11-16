-- Prove2me | Theorems.Thm_SuperRamanujan227_Main_Supplement_theorem_1_2
-- name    : SuperRamanujan227.Main.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:44:35.529539+00:00
-- url     : https://prove2.me/theorems/1320e047-58d2-493b-b5ef-f63f8f686d75
-- title:
--   Theorem 1.2 — Polynomial-time bipartite construction
-- statement:
--   There is a single deterministic algorithm with constants $C>0$ and $k\in\mathbb N$ such that, for every even integer $n$ and integer $3\le d\le n/2$, it outputs a $d$-regular bipartite multigraph $G$ on $n$ vertices in at most $C(n+1)^k$ machine steps, satisfying
--
--   $$\lambda(G)\le2\sqrt{d-1}-\frac{\sqrt d}{2n}.$$
--
--   The parameter $\lambda$ is the two-sided nontrivial adjacency spectral radius with multiplicity. This provides a uniform finite-size improvement for every admissible pair of parameters. The paper's polynomial-time notation is retained as an existential polynomial bound; no numerical runtime degree is asserted.
--
--   Differences from the source:
--   - encoding: an algorithm running in time poly(n) → one finite binary multi-stack machine with uniform bound C(n+1)^k; reason: fixed finite machine instructions and framed binary encodings preserve polynomial bit time; the constants precede all inputs
--   - encoding: the largest absolute nontrivial eigenvalue → maximum after deleting one top eigenvalue and, for a bipartite graph, one bottom eigenvalue, with multiplicity; reason: this removes the canonical trivial directions and retains extra copies in disconnected graphs
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), p. 5, Theorem 1.2

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Supplement_Spectral
import Definitions.Def_SuperRamanujan227_Main_Supplement_Computation

namespace SuperRamanujan227.Main.Supplement

/-- Theorem 1.2, p.5. A single finite machine and polynomial time bound work for all n,d. -/
theorem theorem_1_2 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C k : ℕ), 0 < C ∧
      ∀ (n d : ℕ), Even n → 3 ≤ d → d ≤ n / 2 →
        ∃ G : Multigraph n, G.IsRegular d ∧ MatrixBipartite G.adj ∧
          spectralRadius G ≤ 2 * Real.sqrt ((d : ℝ) - 1) - Real.sqrt d / (2 * (n : ℝ)) ∧
          Runs M (graphInput n d) (graphOutput G) (C * (n + 1)^k) := by sorry

end SuperRamanujan227.Main.Supplement
