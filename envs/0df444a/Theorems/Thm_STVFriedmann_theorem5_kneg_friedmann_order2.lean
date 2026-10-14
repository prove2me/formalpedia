-- Prove2me | Theorems.Thm_STVFriedmann_theorem5_kneg_friedmann_order2
-- name    : STVFriedmann.theorem5_kneg_friedmann_order2
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T02:01:01.280081+00:00
-- url     : https://prove2.me/theorems/a21be30e-e25a-4efa-bd57-b132b846b825
-- title:
--   Theorem 5 (n = 2): the k < 0 Friedmann spacetime in the order-2 STV ODE
-- statement:
--   Fix $\Delta_0>0$ and use $\tilde z_2,\tilde w_0$ from (2.41) together with
--
--   $$
--   \tilde z_4(\theta)=\frac{30(\sinh2\theta-2\theta)^4\cosh^2\theta}{(\cosh2\theta-1)^6},\qquad
--   \tilde w_2(\theta)=\frac{3(\sinh2\theta-2\theta)^3\cosh\theta}{2(\cosh2\theta-1)^4\sinh\theta}
--   $$
--
--   from (2.43). Then there is a solution $(z_2,w_0,z_4,w_2)(\bar t)$, $\bar t\in(0,\infty)$, of the order-2 STV ODE (2.48)–(2.51) such that
--
--   1. $(z_2,w_0,z_4,w_2)(\bar t)=(\tilde z_2,\tilde w_0,\tilde z_4,\tilde w_2)(\theta)$ whenever $\bar t=\tfrac{\Delta_0}{2}(\sinh2\theta-2\theta)$, $\theta>0$;
--   2. the solution tends to $SM=(\tfrac43,\tfrac23,\tfrac{40}{27},\tfrac29)$ as $\bar t\to0^+$;
--   3. the solution tends to $M=(0,1,0,0)$ as $\bar t\to\infty$.
--
--   This is the projection of the $k=-1$ Friedmann spacetime onto the STV ODE of order 2 (the blue curve $\Sigma_4^-$ of Figure 3).
--
--   **Formalization Note** As for order 1, solutions are functions of log-time $\tau=\ln\bar t\in\mathbb R$ satisfying $dU/d\tau=F_2(U)$.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 14, Theorem 5 eqs. (2.41)-(2.43); p. 17, Figure 3; p. 18 (projections of the k < 0 Friedmann spacetimes onto orders n = 1, 2)

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Theorem 5, (2.41) and (2.43): for every `Δ₀ > 0`, the order-2 `k = -1` Friedmann curve
`(z̃₂, w̃₀, z̃₄, w̃₂)(θ)`, with `t̄ = Δ₀ (sinh 2θ - 2θ)/2`, is a solution of the order-2 STV ODE
taking `SM` (as `t̄ → 0`) to `M` (as `t̄ → ∞`). -/
theorem theorem5_kneg_friedmann_order2 (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀) :
    ∃ U : ℝ → Fin 4 → ℝ, IsSTVSolution stvField2 U ∧
      (∀ θ : ℝ, 0 < θ → U (Real.log (Δ₀ * bigBangTime θ)) = friedmannCurve2 θ) ∧
      Tendsto U atBot (𝓝 restSM2) ∧ Tendsto U atTop (𝓝 restM2) := by sorry

end STVFriedmann
