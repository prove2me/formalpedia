-- Prove2me | Theorems.Thm_WeldedPath_Supplement_short_output_sqrt_comparison
-- name    : WeldedPath.Supplement.short_output_sqrt_comparison
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:21:31.580465+00:00
-- url     : https://prove2.me/theorems/04d94a22-429e-45ee-9e38-1b64aff41aec
-- title:
--   Short-output acceptance amplitude versus a recorded crossing
-- statement:
--   There is an absolute constant $C>0$ such that, whenever $N_l\ge80(q+1)$,
--   $$
--   \sqrt{p_{\mathrm{wt}}^{\le}}\le
--   \sqrt{p_{\mathrm{cross}}}+C\sqrt{\frac{q}{N_l}}.
--   $$
--   For each short output, one coherently recovers the structural vertices from its labels and forms the edge-assignment tests $f_{\omega,b}$. Lemma 3.11 transfers these tests to the edge database with error $O(\sqrt{q/N_l})$. Every recorded assignment describing an accepted entrance--exit walk contains a crossing from column $n-l-1$ to column $n+l+1$, so the database-side norm is at most $\sqrt{p_{\mathrm{cross}}}$. The statement is exactly the paper's norm comparison before the final squaring step.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), proof of Theorem 3.12, short-output case, p.26 (printed p.25), construction of Pi_AP and Pi_AC, application of Lemma 3.11, and domination by Pi_Cross.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pWtSplit

open WeldedPath WeldedPath.Supplement QAlgorithms

/-- The short-output assignment comparison in the proof of Theorem 3.12, before squaring
the norms. -/
theorem WeldedPath.Supplement.short_output_sqrt_comparison :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      80 * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      Real.sqrt (pWtLe l G A out) ≤
        Real.sqrt (pCross l G A) + C * Real.sqrt ((q : ℝ) / (2 : ℝ) ^ (n - l)) := by sorry
