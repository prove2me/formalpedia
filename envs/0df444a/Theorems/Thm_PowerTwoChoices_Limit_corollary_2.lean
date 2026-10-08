-- Prove2me | Theorems.Thm_PowerTwoChoices_Limit_corollary_2
-- name    : PowerTwoChoices.Limit.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:14.263702+00:00
-- url     : https://prove2.me/theorems/552e6a10-674f-4144-9143-9aaf78911bbd
-- title:
--   Corollary 2 — the expected time in the limiting supermarket system converges to $T_d(\lambda)=\sum_{i\ge1}\lambda^{(d^i-d)/(d-1)}$
-- statement:
--   Let $d\ge2$ and $0<\lambda<1$, and let
--   $$T_d(\lambda)=\sum_{i=1}^\infty\lambda^{\frac{d^i-d}{d-1}} ,$$
--   which is finite. For a trajectory $s(t)$ of the limiting supermarket system (1), the expected time a customer arriving at time $t$ spends in the system is $E(t)=\sum_{i\ge1}i\,(s_{i-1}(t)^d-s_i(t)^d)$.
--
--   1. If $s_j(0)=0$ for some $j$ (the condition of Theorem 2), then $E(t)\to T_d(\lambda)$ as $t\to\infty$.
--   2. If the system is initially empty, then $E(t)\le T_d(\lambda)$ for all $t\ge0$.
--
--   For $d=1$ the corresponding quantity is the M/M/1 value $1/(1-\lambda)$; $T_d(\lambda)$ for $d\ge2$ is exponentially smaller as $\lambda\to1^-$, which is the "power of two choices".
--
--   **Formalization Note.** $E(t)$ and $T_d(\lambda)$ are computed in $[0,\infty]$; the finiteness of $T_d(\lambda)$ is part of the conclusion, so the convergence is to a real number. Convergence is along real time $t\to\infty$.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1099, Corollary 2

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

open scoped ENNReal
open Filter Topology

namespace PowerTwoChoices.Limit

/-- Corollary 2 (Mitzenmacher 2001, p. 1099). Let `d ≥ 2` and `0 < λ < 1`. The number
`T_d(λ) = ∑_{i ≥ 1} λ^{(d^i-d)/(d-1)}` is finite; for every trajectory of the limiting
supermarket system with `s_j(0) = 0` for some `j` (the condition of Theorem 2), the expected
time `E(t) = ∑_{i ≥ 1} i (s_{i-1}(t)^d - s_i(t)^d)` a customer arriving at time `t` spends in
the system converges to `T_d(λ)` as `t → ∞`; and for the trajectory started from the empty
system, `E(t) ≤ T_d(λ)` for all `t ≥ 0`. -/
theorem corollary_2 (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Td lam d ≠ ⊤ ∧
    (∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s → (∃ j : ℕ, s 0 j = 0) →
      Tendsto (fun t => expectedTime d (s t)) atTop (𝓝 (Td lam d))) ∧
    (∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s → s 0 = emptyState →
      ∀ t : ℝ, 0 ≤ t → expectedTime d (s t) ≤ Td lam d) := by sorry

end PowerTwoChoices.Limit
