-- Prove2me | Theorems.Thm_WaitJudge_Generic_weak_duality_N
-- name    : WaitJudge.Generic.weak_duality_N
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:11:17.503849+00:00
-- url     : https://prove2.me/theorems/0be20ac7-b0e0-4420-8cfb-117c414d4f8b
-- title:
--   (37), pp. 25–26 — weak duality with M=N
-- statement:
--   Fix N and thresholds ε(k)∈[0,1]. Let μ_k be finite nonnegative measures whose first N+1 moment equations agree with the truncated primal problem (35). Let λ_0,…,λ_N satisfy the pointwise dual inequalities (36) with M=N. Then
--
--   $$
--   \sum_{k=0}^{N}{N\choose k}\int_{(\varepsilon(k),1]}(1-v)^{N-k}\,d\mu_k(v)
--   \le \sum_{m=0}^{N}\lambda_m.
--   $$
--
--   This is the finite weak-duality inequality used to pass from the distributional representation of the violation probability to the dual value γ*_N.
--
--   **Formalization Note** The dual variable is a function on natural numbers, but only indices at most N occur. The dual inequalities use t=1−v, so v∈(ε(k),1] becomes t∈[0,1−ε(k)). Finiteness of the measures ensures the displayed real integrals have their intended values.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF pp. 25–26, (35)–(37), specialized to M=N

import Mathlib
import Definitions.Def_WaitJudge_Generic_Setting

namespace WaitJudge.Generic

open MeasureTheory

theorem weak_duality_N
    (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ k ≤ N, 0 ≤ ε k ∧ ε k ≤ 1)
    (μ : ℕ → Measure ℝ)
    (hfinite : ∀ k ≤ N, μ k Set.univ < ⊤)
    (hmoment : ∀ m ≤ N,
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) *
        ∫ v in Set.Icc (0 : ℝ) 1, (1 - v) ^ (m - k) ∂(μ k) = 1)
    (lam : ℕ → ℝ) (hdual : IsFeasibleDualN N ε lam) :
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
      ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(μ k) ≤
    ∑ m ∈ Finset.range (N + 1), lam m := by sorry

end WaitJudge.Generic
