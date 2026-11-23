-- Prove2me | Theorems.Thm_WeldedPath_Supplement_short_output_crossing_bound
-- name    : WeldedPath.Supplement.short_output_crossing_bound
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:34:19.326206+00:00
-- url     : https://prove2.me/theorems/bb69e112-94d8-4f14-8910-69e42556def8
-- title:
--   Short verifier outputs reduce to a recorded crossing
-- statement:
--   Let $n$ be even, $l\in[2,n-4]$, and $N_l=2^{n-l}$. Fix a valid welded trees instance and a $q$-query quantum algorithm $A$, where $q\ge1$. Let $p_{\mathrm{wt}}^{\le}$ be the probability that Algorithm 3.9 accepts and the output has at most $2q+1$ steps, and let $p_{\mathrm{cross}}$ be the probability that the exact compressed execution leaves a recorded crossing. If $N_l\ge80(q+1)$, then
--   $$
--   p_{\mathrm{wt}}^{\le}\le C\left(p_{\mathrm{cross}}+\frac{q}{N_l}\right),
--   $$
--   where $C>0$ is one absolute constant, independent of $n$, $l$, the instance, the finite workspace, $q$, $A$, and its output map.
--
--   This is precisely the short-output contribution estimated in the proof of Theorem 3.12; together with the long-output estimate it gives the verifier-to-crossing comparison.
--
--   **Formalization Note** The probability $p_{\mathrm{wt}}^{\le}$ is the published `pWtLe`, defined by conjoining `Accepts39` with the condition `out.length ≤ 2*q+1`; `pCross` is unchanged.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), proof of Theorem 3.12, short-output case, pp.25–26 (printed pp.24–25)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pWtSplit

namespace WeldedPath.Supplement

open QAlgorithms

/-- The short-output estimate in the proof of Theorem 3.12. -/
theorem short_output_crossing_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      80 * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      pWtLe l G A out ≤ C * (pCross l G A + (q : ℝ) / (2 : ℝ) ^ (n - l)) := by sorry
