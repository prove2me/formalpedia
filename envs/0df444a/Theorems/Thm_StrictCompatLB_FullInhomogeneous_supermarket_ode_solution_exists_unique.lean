-- Prove2me | Theorems.Thm_StrictCompatLB_FullInhomogeneous_supermarket_ode_solution_exists_unique
-- name    : StrictCompatLB.FullInhomogeneous.supermarket_ode_solution_exists_unique
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-18T21:14:15.767361+00:00
-- url     : https://prove2.me/theorems/7e8366de-db6b-4eb1-98a5-2e5d3b97a30f
-- title:
--   Existence and uniqueness of the $\ell_1$-continuous solution of the supermarket ODE (3.3) in $\mathcal{Y}$, $0\le\lambda<1$
-- statement:
--   Let $0\le\lambda<1$ and $d\ge 2$. For every $q_0\in\mathcal{Y}$ (so $q_0(0)=1$, $q_0$ nonnegative and nonincreasing, $\sum_i q_0(i)<\infty$) there is exactly one map $s:[0,\infty)\to\mathbb{R}^{\mathbb{N}}$ with $s(0)=q_0$, $s(t)\in\mathcal{Y}$ for all $t$, $s$ continuous in the $\ell_1$ distance, and solving
--
--   $$\frac{d}{dt}s_i(t)=\lambda\big(s_{i-1}(t)^d-s_i(t)^d\big)-\big(s_i(t)-s_{i+1}(t)\big),\quad i\ge 1,$$
--
--   (one-sided derivative at $t=0$).
--
--   Role: the ODE well-posedness conjunct of Theorem 3.6 (via Theorem 3.4): the deterministic fluid limit exists and is unique for every initial point of $\mathcal{Y}$, including the case $\lambda=0$.
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Theorem 3.4, p. 12 (the ODE (3.3) has a unique solution in Y; cf. Mitzenmacher 2001, IEEE TPDS 12(10), Theorem 1)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model
import Definitions.Def_StrictCompatLB_FullInhomogeneous_Trajectory

open Filter Topology MeasureTheory
open StrictCompatLB.MeanField
open scoped ENNReal NNReal

namespace StrictCompatLB.FullInhomogeneous

theorem supermarket_ode_solution_exists_unique : ∀ (lam : ℝ), 0 ≤ lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
    ∀ q₀ : ℕ → ℝ, InY q₀ → ∃! s : ℝ≥0 → ℕ → ℝ, IsSolution lam d q₀ s := by sorry

end StrictCompatLB.FullInhomogeneous
