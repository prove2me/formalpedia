-- Prove2me | Theorems.Thm_WeldedPath_Supplement_long_output_label_comparison
-- name    : WeldedPath.Supplement.long_output_label_comparison
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:17:56.517748+00:00
-- url     : https://prove2.me/theorems/8ace7628-481b-4587-965a-03ff990768ff
-- title:
--   Long outputs: permutation tests versus recorded inverse labels
-- statement:
--   There is an absolute constant $C>0$ such that, whenever $N_l\ge80(q+1)$, the long-output acceptance amplitude satisfies
--   $$
--   \sqrt{p_{\mathrm{wt}}^{>}}\le
--   \sqrt{p_{\mathrm{long\text{-}label}}}+C\sqrt{\frac{q}{N}}.
--   $$
--   Here $p_{\mathrm{long\text{-}label}$ is the probability of the recorded inverse-label test on the exact compressed final state, restricted to long candidate outputs. The inequality transfers the $2q+1$ inverse-label assignment tests from the random label permutation to its compressed database; the error incorporates the size of $V_n$ and the fact that the long-output component has norm at most one. This is the central norm estimate in the long-output paragraph of Theorem 3.12, with constants absorbed into $C$.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), proof of Theorem 3.12, long-output case, p.26 (printed p.25), application of Lemma 3.11 to the 2q+1 inverse-label tests and the displayed estimate involving ((2q+1)|V_n\{0}|/M)^(1/2).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_pLongLabel

open WeldedPath WeldedPath.Supplement QAlgorithms

/-- The inverse-label assignment comparison for long outputs in the proof of Theorem 3.12,
before squaring the norms. -/
theorem WeldedPath.Supplement.long_output_label_comparison :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      80 * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      Real.sqrt (pWtGt l G A out) ≤
        Real.sqrt (pLongLabel l G A out) + C * Real.sqrt ((q : ℝ) / (2 : ℝ) ^ n) := by sorry
