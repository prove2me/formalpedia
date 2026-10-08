-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_lemma_3_4
-- name    : UniformPrecSched.Makespan.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:31:59.090834+00:00
-- url     : https://prove2.me/theorems/c04767a8-6afd-4fe1-8f8e-1adc805e530d
-- title:
--   Lemma 3.4 — with B_j = {k : p_j/s̄_k > (√K+1)p̄_j}, Σ_k (1/(m_k s̄_k)) Σ_j p_j x̂_kj ≤ (K+√K)D̄
-- statement:
--   Let $K$ be the number of distinct machine speeds, $(\bar x, \bar C, \bar D)$ a feasible solution of LP, $\bar p_j = \sum_k (p_j/\bar s_k)\bar x_{kj}$, $B_j = \{k : p_j/\bar s_k > (\sqrt K + 1)\bar p_j\}$, and $k(j)$ an assignment computed by the assignment algorithm. Let $\hat x_{kj} = 1$ if $k = k(j)$ and $\hat x_{kj} = 0$ otherwise. Then
--   $$\sum_{k=1}^K \frac{1}{m_k\bar s_k}\sum_{j=1}^n p_j\hat x_{kj} \le (K + \sqrt K)\bar D.$$
--
--   This is the load half of Theorem 3.5.
--
--   **Formalization Note** Stated for every feasible solution of LP (the proof uses only (1), (2), (8)).
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 9, Lemma 3.4

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

namespace UniformPrecSched.Makespan

/-- Lemma 3.4 (p. 9), for any feasible solution `(x̄, C̄, D̄)` of `LP` and any assignment `k` computed
by the assignment algorithm with `B_j = {k : p_j/s̄_k > (√K + 1) p̄_j}`: with `x̂_kj = 1` if
`k = k(j)` and `0` otherwise, `Σ_k (1/(m_k s̄_k)) Σ_j p_j x̂_kj ≤ (K + √K) D̄`. -/
theorem lemma_3_4 {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPFeasible I x C D) (k : Assignment I)
    (hk : IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) k) :
    ∑ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * ∑ j, I.p j * xhat I k κ j ≤
      ((numSpeeds I : ℝ) + Real.sqrt (numSpeeds I)) * D := by sorry

end UniformPrecSched.Makespan
