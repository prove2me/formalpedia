-- Prove2me | Theorems.Thm_WaitJudge_Convex_weak_duality
-- name    : WaitJudge.Convex.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:45:09.181737+00:00
-- url     : https://prove2.me/theorems/de388579-c315-4e66-a36e-7199128e976e
-- title:
--   Weak duality between (20) and (21), Sect. 5.1.4, p. 17 — gives (22)
-- statement:
--   Let $d\le M$ and $N$ be natural numbers and $\epsilon(0),\dots,\epsilon(d)\in[0,1]$. Let $F_0,\dots,F_d$ be finite (nonnegative) measures on $\mathbb R$ satisfying the truncated moment conditions of (20),
--   $$\sum_{k=0}^{\min\{m,d\}}\binom mk\int_{[0,1]}(1-v)^{m-k}\,\mathrm dF_k(v)=1,\qquad m=0,1,\dots,M,$$
--   and let $\lambda_0,\dots,\lambda_M\in\mathbb R$ be feasible for the dual problem (21):
--   $$\sum_{m=k}^{M}\lambda_m\binom mk(1-v)^{m-k}\ \ge\ \binom Nk(1-v)^{N-k}\,\mathbf 1_{(\epsilon(k),1]}(v),\qquad v\in[0,1],\ k=0,1,\dots,d.$$
--   Then
--   $$\sum_{k=0}^{d}\binom Nk\int_{(\epsilon(k),1]}(1-v)^{N-k}\,\mathrm dF_k(v)\ \le\ \sum_{m=0}^{M}\lambda_m.$$
--
--   Taking the supremum over $(F_k)$ and the infimum over $\lambda$ gives $\gamma_M\le\gamma^*_M$, hence $\gamma\le\inf_M\gamma^*_M$, which is (22). The statement is pure analysis: no scenario program appears.
--
--   **Formalization Note** The generalized distribution functions of the paper are represented by finite measures on $\mathbb R$; their mass outside $[0,1]$ plays no role. The integrands are bounded on $[0,1]$, so every integral is finite.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF pp. 16–17, Sect. 5.1.4, (20), (21) and the weak-duality chain leading to (22)

import Mathlib

namespace WaitJudge.Convex

theorem weak_duality (d M N : ℕ) (hdM : d ≤ M) (ε : ℕ → ℝ) (hε : ∀ k ≤ d, 0 ≤ ε k ∧ ε k ≤ 1)
    (μ : ℕ → MeasureTheory.Measure ℝ) [∀ k, MeasureTheory.IsFiniteMeasure (μ k)]
    (hmom : ∀ m ≤ M, ∑ k ∈ Finset.range (min m d + 1),
      (m.choose k : ℝ) * ∫ v in Set.Icc 0 1, (1 - v) ^ (m - k) ∂(μ k) = 1)
    (lam : ℕ → ℝ)
    (hlam : ∀ k ≤ d, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (N.choose k : ℝ) * (1 - v) ^ (N - k) * Set.indicator (Set.Ioc (ε k) 1) 1 v ≤
        ∑ m ∈ Finset.Icc k M, lam m * (m.choose k : ℝ) * (1 - v) ^ (m - k)) :
    ∑ k ∈ Finset.range (d + 1), (N.choose k : ℝ) * ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(μ k) ≤
      ∑ m ∈ Finset.range (M + 1), lam m := by sorry

end WaitJudge.Convex
