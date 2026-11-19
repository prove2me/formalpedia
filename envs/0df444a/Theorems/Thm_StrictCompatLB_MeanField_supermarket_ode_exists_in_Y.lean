-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_supermarket_ode_exists_in_Y
-- name    : StrictCompatLB.MeanField.supermarket_ode_exists_in_Y
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:13:37.507186+00:00
-- url     : https://prove2.me/theorems/28317556-bd24-4b09-85ce-4a56237aa368
-- title:
--   Global existence of the supermarket ODE solution in $\mathcal{Y}$
-- statement:
--   Let $0<\lambda<1$ and $d\ge 2$. For every initial point $q_0\in\mathcal{Y}$ (that is, $q_0(0)=1$, $q_0$ nonnegative and nonincreasing, $\sum_i q_0(i)<\infty$) there is a trajectory $s$ of the system
--
--   $$\frac{d}{dt}q_i(t)=\lambda\big(q_{i-1}(t)^d-q_i(t)^d\big)-\big(q_i(t)-q_{i+1}(t)\big),\quad i\ge 1,$$
--
--   with $s(0)=q_0$ and $s(t)\in\mathcal{Y}$ for all $t\ge 0$.
--
--   Role: supplies the fluid trajectory $q^*(t)$ started from an arbitrary point of $\mathcal{Y}$, used in the interchange-of-limits step for the steady state.
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Theorem 3.4, p. 12 (the ODE system and its unique solution in Y; cf. Mitzenmacher 2001, IEEE TPDS 12(10), Theorem 1)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

theorem supermarket_ode_exists_in_Y : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d → ∀ q₀ : ℕ → ℝ, InY q₀ →
    ∃ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s ∧
      (∀ t : ℝ, 0 ≤ t → InY (s t)) ∧ s 0 = q₀ := by sorry

end StrictCompatLB.MeanField
