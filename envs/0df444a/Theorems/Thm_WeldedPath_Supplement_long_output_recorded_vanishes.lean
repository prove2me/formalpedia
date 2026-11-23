-- Prove2me | Theorems.Thm_WeldedPath_Supplement_long_output_recorded_vanishes
-- name    : WeldedPath.Supplement.long_output_recorded_vanishes
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:28.575778+00:00
-- url     : https://prove2.me/theorems/f9a8bf71-c674-4a66-8672-3e0df9c78de9
-- title:
--   Long candidate outputs cannot pass the recorded inverse-label test
-- statement:
--   For every $q$-query exact compressed execution, the recorded long-output inverse-label probability is zero:
--   $$
--   p_{\mathrm{long\text{-}label}}=0.
--   $$
--   After $q$ queries the label database has at most $2q$ records. On the other hand, a candidate output has pairwise distinct labels, and passing the long-output recorded test would give inverse records for its first $2q+1$ labels. Injectivity of the partial inverse label map therefore makes the test impossible. The remaining hypotheses retain the uniform setting of Theorem 3.12 and are not used in this combinatorial annihilation step.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), proof of Theorem 3.12, long-output case, p.26 (printed p.25), Observation 3.7 support bound |L| ≤ 2q and the statement that acceptance requiring at least 2q+1 records annihilates the final state; candidate-path distinctness from Algorithm 3.9, p.24 (printed p.23).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pLongLabel

open WeldedPath WeldedPath.Supplement QAlgorithms

/-- The recorded inverse-label test vanishes because an exact compressed execution after
`q` queries has at most `2*q` label records, whereas a long candidate output supplies
`2*q+1` distinct labels. -/
theorem WeldedPath.Supplement.long_output_recorded_vanishes :
    ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedInstance n, G.IsValid →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
    ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
      (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
        List (Fin 3 × Qubits (2 * n + 1))),
    pLongLabel l G A out = 0 := by sorry
