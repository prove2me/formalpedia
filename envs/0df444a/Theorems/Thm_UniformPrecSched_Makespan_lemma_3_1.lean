-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_lemma_3_1
-- name    : UniformPrecSched.Makespan.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:31:28.181872+00:00
-- url     : https://prove2.me/theorems/d856fc49-8788-4ced-9f0f-df2552c8346e
-- title:
--   Lemma 3.1 — with B_j = {k : p_j/s̄_k > 2p̄_j}, every chain has Σ p_j/s̄_{k(j)} ≤ 2D̄
-- statement:
--   Let $(\bar x, \bar C, \bar D)$ be a feasible solution of LP, $\bar p_j = \sum_k (p_j/\bar s_k)\bar x_{kj}$, and $B_j = \{k : p_j/\bar s_k > 2\bar p_j\}$. The assignment algorithm computes values $k(j)$ (an index $k \notin B_j$ maximizing $\bar s_k m_k$; such an index exists), and for every assignment it can compute and every chain of jobs $\mathcal C$,
--   $$\sum_{j \in \mathcal C} \frac{p_j}{\bar s_{k(j)}} \le 2\bar D.$$
--
--   Together with Lemma 3.2 it gives the $2(K+1)$ guarantee; Lemma 3.3 is its refinement with threshold $\sqrt K + 1$.
--
--   **Formalization Note** The paper states the lemma for the optimal solution of LP; its proof uses only constraints (3), (4), (5), so it is stated here for every feasible solution. The existence of an assignment is part of the statement ("computes values $k(j)$").
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 7, Lemma 3.1

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

namespace UniformPrecSched.Makespan

/-- Lemma 3.1 (p. 7), for any feasible solution `(x̄, C̄, D̄)` of `LP`: the assignment algorithm with
`B_j = {k : p_j/s̄_k > 2 p̄_j}` computes values `k(j)`, and for every such `k` and each chain of
jobs `𝒞`, `Σ_{j ∈ 𝒞} p_j / s̄_{k(j)} ≤ 2 D̄`. -/
theorem lemma_3_1 {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) :
    (∃ k, IsLPAssignment I x 2 k) ∧
      ∀ k, IsLPAssignment I x 2 k → ∀ c, IsJobChain I c → chainLength I k c ≤ 2 * D := by sorry

end UniformPrecSched.Makespan
