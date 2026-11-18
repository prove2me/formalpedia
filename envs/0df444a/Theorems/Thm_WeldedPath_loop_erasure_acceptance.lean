-- Prove2me | Theorems.Thm_WeldedPath_loop_erasure_acceptance
-- name    : WeldedPath.loop_erasure_acceptance
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T16:28:56.153232+00:00
-- url     : https://prove2.me/theorems/6a02e3c0-9c15-4f62-a25b-b305c5dd4029
-- title:
--   Loop erasure makes successful entrance-exit walks pass Algorithm 3.9
-- statement:
--   Let $n\ge16$ be even, $2\le l\le n-4$, and let $G$ be a valid properly three-colored welded-tree instance. There is one map $E$ on finite lists of colored labels, chosen before the sampled oracle $\sigma$ and query count $q$, such that for every $\sigma$ in the single-cycle support, every $q\ge1$, and every output list $x$,
--   $$
--   x\text{ is an entrance--exit walk in }\sigma
--   \quad\Longrightarrow\quad
--   \operatorname{Accepts}_{3.9}(\sigma,q,E(x)).
--   $$
--   Thus a successful walk admits deterministic postprocessing that makes it acceptable to the path verifier, without additional queries or knowledge of the sampled oracle. This isolates loop removal and verifier completeness from the probability and quantum-query distribution comparisons. The map is uniform over all query counts and sampled oracles for the fixed graph parameters.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/pdf/2611.05912v1. Section 3.3, paragraph introducing candidate paths and loop removal immediately before Algorithm 3.9 (PDF p.23), and Algorithm 3.9 (PDF p.24); Section 4.5, first inequality in the proof of Theorem 4.1 (PDF p.44). The existential map makes oracle-independent postprocessing explicit for the published walk-based success predicate.

import Definitions.Def_WeldedPath_Supplement_pWt

namespace WeldedPath

open QAlgorithms Supplement

/-- A single postprocessing map, independent of the sampled oracle and query count,
turns every successful entrance--exit walk into an output accepted by Algorithm 3.9.
This is the loop-removal and verifier-completeness observation in Section 3.3 of
Carolan et al., arXiv:2611.05912v1, immediately before Algorithm 3.9.

The map can be chosen by chronological loop erasure on the output labels. The remaining
graph facts are that oracle edges change structural column by one, the entrance and exit
are in columns 0 and 2n+1, and the exit has precisely two nontrivial colors. -/
theorem loop_erasure_acceptance
    (n l : ℕ) (hnEven : Even n) (hn : 16 ≤ n) (hl : 2 ≤ l) (hlmax : l ≤ n - 4)
    (G : WeldedInstance n) (hG : G.IsValid) :
    ∃ erase : List (Fin 3 × Qubits (2 * n + 1)) →
        List (Fin 3 × Qubits (2 * n + 1)),
      ∀ σ : Equiv.Perm (Label n) × Equiv.Perm G.edges,
        σ ∈ G.singSupport l →
        ∀ (xs : List (Fin 3 × Qubits (2 * n + 1))) (q : ℕ), 1 ≤ q →
          G.IsEntranceExitWalk l σ xs → Accepts39 l G σ q (erase xs) := by sorry

end WeldedPath
