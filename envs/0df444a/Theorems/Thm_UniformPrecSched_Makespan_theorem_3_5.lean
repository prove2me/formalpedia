-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_theorem_3_5
-- name    : UniformPrecSched.Makespan.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:32:13.798983+00:00
-- url     : https://prove2.me/theorems/1f4dea90-f661-40bf-89b1-9e0f2a4c4318
-- title:
--   Theorem 3.5 — LP-based assignment + speed-based list scheduling is a (K + 2√K + 1)-approximation
-- statement:
--   Let $I$ be an instance of $Q|prec|C_{\max}$ with $K$ distinct machine speeds. Let $(\bar x, \bar C, \bar D)$ be an optimal solution of LP, let $k(j)$ be an assignment computed by the assignment algorithm with $B_j = \{k : p_j/\bar s_k > (\sqrt K+1)\bar p_j\}$, and let $\sigma$ be a schedule produced by the speed-based list scheduling algorithm for $k$. Then for every feasible schedule $\sigma^*$ of $I$,
--   $$C_{\max}(\sigma) \le (K + 2\sqrt K + 1)\, C_{\max}(\sigma^*).$$
--   That is, the combined algorithm is a $(K + 2\sqrt K + 1)$-approximation algorithm.
--
--   It is the first branch of the guarantee of Theorem 3.7.
--
--   **Formalization Note** The comparator is every feasible schedule of the same instance, which is equivalent to comparing with the optimal length $C^*_{\max}$ without assuming an optimum is attained. Polynomial running time is not formalized.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 9, Theorem 3.5

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

namespace UniformPrecSched.Makespan

/-- Theorem 3.5 (p. 9): the assignment algorithm (from an optimal solution of `LP`, with
`B_j = {k : p_j/s̄_k > (√K + 1) p̄_j}`) combined with the speed-based list scheduling algorithm
produces a schedule of length at most `(K + 2√K + 1)` times the length of any feasible schedule,
where `K` is the number of distinct machine speeds. -/
theorem theorem_3_5 {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPOptimal I x C D) (k : Assignment I)
    (hk : IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) k) (σ : Schedule I)
    (hσ : IsSpeedListSchedule I k σ) (σstar : Schedule I) :
    σ.makespan ≤
      ((numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1) * σstar.makespan := by sorry

end UniformPrecSched.Makespan
