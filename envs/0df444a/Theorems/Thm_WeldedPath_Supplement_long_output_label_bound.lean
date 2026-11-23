-- Prove2me | Theorems.Thm_WeldedPath_Supplement_long_output_label_bound
-- name    : WeldedPath.Supplement.long_output_label_bound
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:35:15.974153+00:00
-- url     : https://prove2.me/theorems/e87eb465-b54e-4e6e-a02f-b8004c67a13f
-- title:
--   Long verifier outputs have $O(q/N_l)$ acceptance probability
-- statement:
--   Let $n$ be even, $l\in[2,n-4]$, and $N_l=2^{n-l}$. Fix a valid welded trees instance and a $q$-query quantum algorithm $A$, where $q\ge1$. Let $p_{\mathrm{wt}}^{>}$ be the probability that Algorithm 3.9 accepts and the output has more than $2q+1$ steps. If $N_l\ge80(q+1)$, then
--   $$
--   p_{\mathrm{wt}}^{>}\le C\,\frac{q}{N_l},
--   $$
--   where $C>0$ is one absolute constant, independent of all these data.
--
--   This is the long-output contribution required by Theorem 3.12. The source proves the slightly sharper bound $O(q/N)$ with $N=2^n$; the displayed statement follows because $N_l\le N$.
--
--   **Formalization Note** The probability $p_{\mathrm{wt}}^{>}$ is the published `pWtGt`, defined by conjoining `Accepts39` with the condition `2*q+1 < out.length`. The size hypothesis retained here is the one already assumed by Theorem 3.12.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), proof of Theorem 3.12, long-output case and final inequality $N_l\le N$, p.26 (printed p.25)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pWtSplit

namespace WeldedPath.Supplement

open QAlgorithms

/-- The long-output estimate in the proof of Theorem 3.12. -/
theorem long_output_label_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      80 * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      pWtGt l G A out ≤ C * ((q : ℝ) / (2 : ℝ) ^ (n - l)) := by sorry
