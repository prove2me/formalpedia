-- Prove2me | Theorems.Thm_UniformPrecSched_Makespan_corollary_3_6
-- name    : UniformPrecSched.Makespan.corollary_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:32:26.566622+00:00
-- url     : https://prove2.me/theorems/d376d94e-dbba-4207-bab8-6cd1793bbb02
-- title:
--   Corollary 3.6 — the schedule has C_max ≤ (K + 2√K + 1)D̄
-- statement:
--   Let $I$ be an instance of $Q|prec|C_{\max}$ with $K$ distinct machine speeds, $(\bar x, \bar C, \bar D)$ an optimal solution of LP with optimal value $\bar D$, $k(j)$ an assignment computed by the assignment algorithm with $B_j = \{k : p_j/\bar s_k > (\sqrt K+1)\bar p_j\}$, and $\sigma$ a schedule produced by the speed-based list scheduling algorithm for $k$. Then
--   $$C_{\max}(\sigma) \le (K + 2\sqrt K + 1)\,\bar D.$$
--
--   Comparing with the LP value rather than with an optimal schedule is what allows the speed-rounding reduction to be combined with this guarantee.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 9, Corollary 3.6

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

namespace UniformPrecSched.Makespan

/-- Corollary 3.6 (p. 9): the assignment algorithm combined with the speed-based list scheduling
algorithm produces a schedule whose length is at most `(K + 2√K + 1) D̄`, where `D̄` is the optimal
value of `LP`. -/
theorem corollary_3_6 {n m : ℕ} (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) (hLP : LPOptimal I x C D) (k : Assignment I)
    (hk : IsLPAssignment I x (Real.sqrt (numSpeeds I) + 1) k) (σ : Schedule I)
    (hσ : IsSpeedListSchedule I k σ) :
    σ.makespan ≤ ((numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1) * D := by sorry

end UniformPrecSched.Makespan
