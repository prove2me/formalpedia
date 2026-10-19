-- Prove2me | Theorems.Thm_STVFriedmann_theorem7_decay_to_minkowski
-- name    : STVFriedmann.theorem7_decay_to_minkowski
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T02:01:38.335785+00:00
-- url     : https://prove2.me/theorems/969c9d6c-4a03-434c-b438-bc7a06b5805b
-- title:
--   Theorem 7: decay rates of solutions tending to M
-- statement:
--   Let $(z_2,w_0,z_4,w_2)(\bar t)$, $\bar t\in(0,\infty)$, be a solution of the order-2 STV ODE (2.48)–(2.51) that tends to the Minkowski rest point $M=(0,1,0,0)$ as $\bar t\to\infty$. Then there are constants $C$ and $\bar t_0$ such that for all $\bar t\ge\bar t_0$
--
--   $$
--   |z_2(\bar t)|\le \frac{C}{\bar t},\qquad |w_0(\bar t)-1|\le \frac{C\ln\bar t}{\bar t},\qquad
--   |z_4(\bar t)|\le \frac{C}{\bar t},\qquad |w_2(\bar t)|\le \frac{C\ln\bar t}{\bar t}.
--   $$
--
--   Since $z=\kappa\rho\bar r^2=z_2\xi^2+z_4\xi^4+\dots$ and $v=\xi w=w_0\xi+w_2\xi^3+\dots$ with $\xi=\bar r/\bar t$, the order-1 estimates are the STV ODE form of the decay to Minkowski spacetime (2.46)–(2.47), and the order-2 estimates — applied to a solution and to the $k<0$ Friedmann solution it agrees with at leading order — give the discrepancy estimates (2.44)–(2.45).
--
--   **Formalization Note** In log-time $\tau=\ln\bar t$ the bounds read $C e^{-\tau}$ and $C\tau e^{-\tau}$ for all $\tau\ge T$.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 16, Theorem 7 eqs. (2.44)-(2.47) and the preceding paragraph (z_2 and w_0 decay to M like O(t^-1) and O(t^-1 ln t))

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Theorem 7, (2.44)–(2.47), at the level of the order-2 STV ODE: every solution tending to
`M` satisfies `z₂, z₄ = O(1/t̄)` and `w₀ - 1, w₂ = O(ln t̄ / t̄)` as `t̄ → ∞`
(here `τ = ln t̄`). -/
theorem theorem7_decay_to_minkowski (U : ℝ → Fin 4 → ℝ) (hU : IsSTVSolution stvField2 U)
    (hM : Tendsto U atTop (𝓝 restM2)) :
    ∃ C T : ℝ, ∀ τ : ℝ, T ≤ τ →
      |U τ 0| ≤ C * Real.exp (-τ) ∧ |U τ 1 - 1| ≤ C * τ * Real.exp (-τ) ∧
      |U τ 2| ≤ C * Real.exp (-τ) ∧ |U τ 3| ≤ C * τ * Real.exp (-τ) := by sorry

end STVFriedmann
