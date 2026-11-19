-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_supermarket_ode_uniform_exp_decay
-- name    : StrictCompatLB.MeanField.supermarket_ode_uniform_exp_decay
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:21:40.360076+00:00
-- url     : https://prove2.me/theorems/f2147b7a-6a95-4ff4-a398-ac324edce835
-- title:
--   Uniform exponential decay of the weighted $\ell^1$ potential along the supermarket ODE
-- statement:
--   Let $0<\lambda<1$ and $d\ge 2$. There are positive weights $\omega_i$ ($i\ge1$), geometric with ratio $r\in(1,2/(1+\lambda))$ from the index $i_0$ on, and a rate $\delta>0$ such that every trajectory $s$ of the supermarket ODE staying in $\mathcal{Y}$ satisfies, for all $t\ge 0$,
--
--   $$\Psi_\omega(s(t))\le e^{-\delta t}\,\Psi_\omega(s(0)),\qquad \Psi_\omega(q)=\sum_{i\ge1}\omega_i|q_i-q^*_i(\infty)|.$$
--
--   Role: the decay constant does not depend on the trajectory, so fluid trajectories from a compact set of initial points are uniformly close to the fixed point after a fixed time.
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Theorem 4.11, p. 22, in the form with the constant c0 equal to the initial potential (cf. Mitzenmacher 2001, IEEE TPDS 12(10), Theorem 3)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology
open scoped ENNReal

namespace StrictCompatLB.MeanField

theorem supermarket_ode_uniform_exp_decay : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
  ∃ ω : ℕ → ℝ, (∀ i, 1 ≤ i → 0 < ω i) ∧ ∃ r : ℝ, 1 < r ∧ r < 2 / (1 + lam) ∧
    (∀ i : ℕ, 1 ≤ i → ω (i0Index lam d + i) = ω (i0Index lam d) * r ^ i) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
      (∀ t : ℝ, 0 ≤ t → InY (s t)) → ∀ t : ℝ, 0 ≤ t →
        PowerTwoChoices.Limit.potential lam d ω (s t) ≤
          ENNReal.ofReal (Real.exp (-δ * t)) * PowerTwoChoices.Limit.potential lam d ω (s 0) := by sorry

end StrictCompatLB.MeanField
