-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_lemma_3_3
-- name    : UniformPrecSched.Makespan.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:31:57.319653+00:00
-- url     : https://prove2.me/theorems/ecb369f0-60aa-4fb0-831b-eeccd85072da
-- title:
--   Lemma 3.3 — with B_j = {k : p_j/s̄_k > (√K+1)p̄_j}, every chain has Σ p_j/s̄_{k(j)} ≤ (√K+1)D̄
-- statement:
--   Let $K$ be the number of distinct machine speeds, $(\bar x, \bar C, \bar D)$ a feasible solution of LP, $\bar p_j = \sum_k (p_j/\bar s_k)\bar x_{kj}$, and $B_j = \{k : p_j/\bar s_k > (\sqrt K + 1)\bar p_j\}$. The assignment algorithm computes values $k(j)$ (an index $k\notin B_j$ maximizing $\bar s_k m_k$; such an index exists), and for every assignment it can compute and every chain of jobs $\mathcal C$,
--   $$\sum_{j\in\mathcal C}\frac{p_j}{\bar s_{k(j)}} \le (\sqrt K + 1)\bar D.$$
--
--   This is the chain half of Theorem 3.5.
--
--   **Formalization Note** Stated for every feasible solution of LP (the proof uses only (3), (4), (5)); the existence of an assignment is part of the statement.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 8, Lemma 3.3 (with the modified B_j of p. 8)

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

namespace UniformPrecSched.Makespan

/-- Lemma 3.3 (p. 8), for any feasible solution `(x̄, C̄, D̄)` of `LP`: the assignment algorithm with
`B_j = {k : p_j/s̄_k > (√K + 1) p̄_j}` computes values `k(j)`, and for every such `k` and each chain
of jobs `𝒞`, `Σ_{j ∈ 𝒞} p_j / s̄_{k(j)} ≤ (√K + 1) D̄`. -/
theorem lemma_3_3 {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) :
    (∃ k, IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) k) ∧
      ∀ k, IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) k →
        ∀ c, IsJobChain I c → chainLength I k c ≤ (Real.sqrt (numSpeeds I) + 1) * D := by sorry

end UniformPrecSched.Makespan
