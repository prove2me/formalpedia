-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_lemma_3_2
-- name    : UniformPrecSched.Makespan.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:31:44.636365+00:00
-- url     : https://prove2.me/theorems/48d8f504-3144-4ec7-8c9a-19b0f6bf8047
-- title:
--   Lemma 3.2 — with B_j = {k : p_j/s̄_k > 2p̄_j}, Σ_k (1/(m_k s̄_k)) Σ_j p_j x̂_kj ≤ 2KD̄
-- statement:
--   Let $(\bar x, \bar C, \bar D)$ be a feasible solution of LP, $\bar p_j = \sum_k (p_j/\bar s_k)\bar x_{kj}$, $B_j = \{k : p_j/\bar s_k > 2\bar p_j\}$, and let $k(j)$ be an assignment computed by the assignment algorithm (for each $j$, an index $k\notin B_j$ maximizing $\bar s_k m_k$). Let $\hat x_{kj} = 1$ if $k = k(j)$ and $\hat x_{kj} = 0$ otherwise. Then
--   $$\sum_{k=1}^K \frac{1}{m_k \bar s_k}\sum_{j=1}^n p_j \hat x_{kj} \le 2K\bar D,$$
--   where $K$ is the number of distinct machine speeds.
--
--   The left-hand side is $\sum_k D_k$ for the assignment $k$, the load term of Theorem 2.1.
--
--   **Formalization Note** As for Lemma 3.1, the statement is made for every feasible solution of LP (the proof uses only (1), (2), (8)).
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 7, Lemma 3.2

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

namespace UniformPrecSched.Makespan

/-- Lemma 3.2 (p. 7), for any feasible solution `(x̄, C̄, D̄)` of `LP` and any assignment `k` computed
by the assignment algorithm with `B_j = {k : p_j/s̄_k > 2 p̄_j}`: with `x̂_kj = 1` if `k = k(j)` and
`0` otherwise, `Σ_k (1/(m_k s̄_k)) Σ_j p_j x̂_kj ≤ 2 K D̄`. -/
theorem lemma_3_2 {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) (k : Assignment I)
    (hk : IsLPAssignment I x 2 k) :
    ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * ∑ j, I.p j * xhat I k κ j ≤
      2 * (numSpeeds I : ℝ) * D := by sorry

end UniformPrecSched.Makespan
